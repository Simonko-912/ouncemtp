/*
 * OunceMTP - usb:ds transport (Switch / Switch 2 via libounce).
 * SPDX-License-Identifier: ISC
 *
 * Presents the console as a standard MTP device: one interface, class
 * 0x06/0x01/0x01 (Still Image / PTP) with the string "MTP", bulk IN + bulk
 * OUT + interrupt IN. Windows, macOS (via OpenMTP / Android File Transfer)
 * and Linux (libmtp / gvfs / KIO) bind their built-in MTP drivers to that
 * without any driver install, which is the point of using MTP over a
 * custom usbComms protocol.
 *
 * VID:PID 057e:201d is the one Atmosphère's "haze" MTP server uses, and is
 * in libmtp's device table, so Linux applies the right quirk flags.
 *
 * Every wait is sliced (WAIT_SLICE_NS) so the worker notices the stop flag
 * and cable pulls promptly instead of blocking forever inside usb:ds.
 *
 * ---- Switch 2 ------------------------------------------------------------
 * Switch 2's usb:ds answers with result module 293 (no Switch 1 service uses
 * it) and is undocumented. Found on hardware (firmware of November 2026):
 *  - IDsService commands match Switch 1 11.0.0+ (bind, RegisterInterface,
 *    GetState, string / device descriptors, BOS, Enable, GetSpeed).
 *  - IDsInterface does not. cmd 0 RegisterEndpoint and cmd 1 GetSetupEvent
 *    are unchanged, but AppendConfigurationData is cmd 6 (Switch 1: 10; same
 *    arguments, u32 speed + map-alias buffer); cmd 5 (Switch 1:
 *    GetCtrlInCompletionEvent) fails with 2293-0605; and a request in the
 *    wrong shape makes usb:ds close the session (2001-0123). Scans of cmd
 *    0-15: config shape "xxxxxxouxxxxxxxx", event-getter shape
 *    "xoxxxuxxxxxxxxxx" (o ok, x closed, u module-293 error).
 *  - IDsEndpoint is unchanged: cmd 0 PostBufferAsync, 2 GetCompletionEvent,
 *    3 GetReportData all work.
 * So the interface and endpoints are registered here rather than through
 * libounce (whose usbDsRegisterInterface fetches the ctrl events, which MTP
 * never uses, and whose AppendConfigurationData sends cmd 10), and the
 * configuration call follows a "plan": the Switch 2 form first, and if that
 * fails (e.g. a later firmware moves it again, or this runs on a Switch 1),
 * probe() tries the other plausible forms in throwaway sessions, logs what it
 * finds, and setup is retried with the first form that works. libounce's
 * endpoint calls (post / cancel / report) only use the object's own session
 * and are used unchanged.
 */
#include "transport.h"
#include "status.h"

#include <stdio.h>
#include <string.h>
#include <switch.h>

#define MTP_VID 0x057e
#define MTP_PID 0x201d
#define WAIT_SLICE_NS 100000000ull   /* 100 ms */
#define MAX_INTERFACE_SLOTS 4        /* libnx's TOTAL_INTERFACES */
#define RC_SESSION_CLOSED 0xF601u    /* KernelError_ConnectionClosed: 2001-0123 */

static UsbDsInterface  g_intf_obj;
static UsbDsEndpoint   g_ep_obj[3];
static UsbDsInterface *g_intf;
static UsbDsEndpoint  *g_ep_in, *g_ep_out, *g_ep_irq;
static bool     g_rd_posted, g_wr_posted;
static u32      g_rd_urb, g_wr_urb;
static u32      g_mps = 512;
static Result   g_last_rc;
static const char *g_fail_step = "";
static volatile int *g_stop;
static char     g_serial[32] = "OUNCEMTP0001";

void tp_set_stop_flag(volatile int *flag) { g_stop = flag; }
void tp_set_serial(const char *serial)
{
    if (serial && serial[0]) {
        strncpy(g_serial, serial, sizeof(g_serial) - 1);
        g_serial[sizeof(g_serial) - 1] = 0;
    }
}
u32 tp_last_result(void) { return g_last_rc; }
const char *tp_last_step(void) { return g_fail_step; }

static bool stopping(void) { return g_stop && *g_stop; }

/* A fatal setup step: records which call failed, for the error screen. */
#define TRY(step, x) do { Result _rc = (x); if (R_FAILED(_rc)) { g_last_rc = _rc; g_fail_step = (step); return TP_ERROR; } } while (0)

/* Short form for the activity list: "ok", "closed", "u605" (usb:ds module
 * 293), or the full 2XXX-YYYY code. */
static void rc_short(char *out, size_t n, Result rc)
{
    if (R_SUCCEEDED(rc))                 snprintf(out, n, "ok");
    else if (rc == RC_SESSION_CLOSED)    snprintf(out, n, "closed");
    else if (R_MODULE(rc) == 293)        snprintf(out, n, "u%u", R_DESCRIPTION(rc));
    else                                 snprintf(out, n, "%04u-%04u", 2000 + R_MODULE(rc), R_DESCRIPTION(rc));
}

/* One character per result, for command scans. */
static char rc_char(Result rc)
{
    if (R_SUCCEEDED(rc))              return 'o';
    if (rc == RC_SESSION_CLOSED)      return 'x';
    if (R_MODULE(rc) == 293)          return 'u';
    if (R_MODULE(rc) == 10 || R_MODULE(rc) == 11) return 's';
    if (R_MODULE(rc) == 1)            return 'k';
    return '?';
}

/* ---- the configuration-call plan ------------------------------------------- */

typedef enum { BUF_MAP, BUF_AUTO, BUF_PTR } buf_kind_t;

typedef struct {
    u32        cmd;     /* IDsInterface command for AppendConfigurationData */
    buf_kind_t buf;     /* how the descriptor buffer is passed */
    bool       pre11;   /* {u8 interface, pad, u32 speed} instead of u32 speed */
    bool       blob;    /* whole descriptor set in one call per speed */
    bool       full;    /* also register USB 1 Full-Speed */
    bool       super;   /* also register USB 3 SuperSpeed */
} usb_plan_t;

/* libnx / haze on Switch 1 (11.0.0+). */
static const usb_plan_t k_libnx_plan = { 10, BUF_MAP, false, false, true, true };
/* Switch 2, found by probe() on hardware: same arguments, cmd 6. */
static const usb_plan_t k_switch2_plan = { 6, BUF_MAP, false, false, true, true };

static const char *buf_name(buf_kind_t b) { return b == BUF_AUTO ? "auto" : b == BUF_PTR ? "ptr" : "map"; }

/* ---- interface / endpoint objects ------------------------------------------ */

/* IDsService cmd 1 (RegisterInterface) on the first free slot. */
static Result register_interface(void)
{
    Service *ds = usbDsGetServiceSession();
    Result rc = 0;
    for (u8 slot = 0; slot < MAX_INTERFACE_SLOTS; slot++) {
        memset(&g_intf_obj, 0, sizeof(g_intf_obj));
        serviceAssumeDomain(ds);
        rc = serviceDispatchIn(ds, 1, slot, .out_num_objects = 1, .out_objects = &g_intf_obj.s);
        if (R_SUCCEEDED(rc)) {
            g_intf_obj.initialized = true;
            g_intf_obj.interface_index = slot;
            g_intf = &g_intf_obj;
            return 0;
        }
    }
    return rc;
}

/* IDsInterface cmd 0 (RegisterEndpoint), then IDsEndpoint cmd 2
 * (GetCompletionEvent), which the transfers wait on. `*event_step` tells the
 * caller which of the two failed. */
static Result register_endpoint(UsbDsEndpoint *ep, u8 address, bool *event_step)
{
    *event_step = false;
    memset(ep, 0, sizeof(*ep));
    serviceAssumeDomain(&g_intf->s);
    Result rc = serviceDispatchIn(&g_intf->s, 0, address, .out_num_objects = 1, .out_objects = &ep->s);
    if (R_FAILED(rc)) return rc;
    ep->initialized = true;

    *event_step = true;
    Handle h = INVALID_HANDLE;
    serviceAssumeDomain(&ep->s);
    rc = serviceDispatch(&ep->s, 2, .out_handle_attrs = { SfOutHandleAttr_HipcCopy }, .out_handles = &h);
    if (R_SUCCEEDED(rc)) eventLoadRemote(&ep->CompletionEvent, h, false);
    return rc;
}

/* Closes the endpoint and interface objects. Must run before usbDsExit(),
 * which closes the session they live in. Harmless after usb:ds has already
 * closed the session itself. */
static void release_objects(void)
{
    for (int i = 0; i < 3; i++) {
        UsbDsEndpoint *ep = &g_ep_obj[i];
        if (!ep->initialized) continue;
        usbDsEndpoint_Cancel(ep);
        eventClose(&ep->CompletionEvent);
        serviceAssumeDomain(&ep->s);
        serviceClose(&ep->s);
        ep->initialized = false;
    }
    if (g_intf_obj.initialized) {
        serviceAssumeDomain(&g_intf_obj.s);
        serviceClose(&g_intf_obj.s);
        g_intf_obj.initialized = false;
    }
    g_intf = NULL;
    g_ep_in = g_ep_out = g_ep_irq = NULL;
    g_rd_posted = g_wr_posted = false;
}

/* ---- descriptors ------------------------------------------------------------- */

typedef struct {
    struct usb_interface_descriptor intf;
    struct usb_endpoint_descriptor  in, out, irq;
} mtp_descs_t;

static const struct usb_ss_endpoint_companion_descriptor k_comp_bulk = {
    .bLength = sizeof(struct usb_ss_endpoint_companion_descriptor),
    .bDescriptorType = USB_DT_SS_ENDPOINT_COMPANION,
    .bMaxBurst = 0x0F,           /* 16-packet bursts: matters for USB 3 throughput */
};
static const struct usb_ss_endpoint_companion_descriptor k_comp_irq = {
    .bLength = sizeof(struct usb_ss_endpoint_companion_descriptor),
    .bDescriptorType = USB_DT_SS_ENDPOINT_COMPANION,
    .wBytesPerInterval = 0x18,
};

/* BOS: USB 2.0 LPM + SuperSpeed capability, required for USB 3 hosts. */
static const u8 k_bos[0x16] = {
    0x05, USB_DT_BOS, 0x16, 0x00, 0x02,
    0x07, USB_DT_DEVICE_CAPABILITY, 0x02, 0x02, 0x00, 0x00, 0x00,
    0x0A, USB_DT_DEVICE_CAPABILITY, 0x03, 0x00, 0x0E, 0x00, 0x03, 0x00, 0x00, 0x00,
};

static void fill_descs(mtp_descs_t *d, u8 slot, u8 iInterface)
{
    *d = (mtp_descs_t){
        .intf = {
            .bLength            = USB_DT_INTERFACE_SIZE,
            .bDescriptorType    = USB_DT_INTERFACE,
            .bInterfaceNumber   = slot,
            .bNumEndpoints      = 3,
            .bInterfaceClass    = 0x06,  /* Still Image */
            .bInterfaceSubClass = 0x01,
            .bInterfaceProtocol = 0x01,  /* PIMA 15740 bulk-only */
            .iInterface         = iInterface,
        },
        .in = {
            .bLength = USB_DT_ENDPOINT_SIZE, .bDescriptorType = USB_DT_ENDPOINT,
            .bEndpointAddress = USB_ENDPOINT_IN + slot + 1,
            .bmAttributes = USB_TRANSFER_TYPE_BULK,
        },
        .out = {
            .bLength = USB_DT_ENDPOINT_SIZE, .bDescriptorType = USB_DT_ENDPOINT,
            .bEndpointAddress = USB_ENDPOINT_OUT + slot + 1,
            .bmAttributes = USB_TRANSFER_TYPE_BULK,
        },
        .irq = {
            .bLength = USB_DT_ENDPOINT_SIZE, .bDescriptorType = USB_DT_ENDPOINT,
            .bEndpointAddress = USB_ENDPOINT_IN + slot + 2,
            .bmAttributes = USB_TRANSFER_TYPE_INTERRUPT, .wMaxPacketSize = 0x18, .bInterval = 0x06,
        },
    };
}

/* One AppendConfigurationData call in the plan's form. */
static Result append_raw(const usb_plan_t *p, UsbDeviceSpeed speed, const void *buf, size_t size)
{
    const u32 attr = SfBufferAttr_In | (p->buf == BUF_AUTO ? SfBufferAttr_HipcAutoSelect
                                      : p->buf == BUF_PTR  ? SfBufferAttr_HipcPointer
                                                           : SfBufferAttr_HipcMapAlias);
    serviceAssumeDomain(&g_intf->s);
    if (p->pre11) {
        const struct { u8 intf_num; u8 pad[3]; u32 speed; } in = { g_intf->interface_index, {0}, speed };
        return serviceDispatchIn(&g_intf->s, p->cmd, in, .buffer_attrs = { attr }, .buffers = { { buf, size } });
    }
    const u32 in = speed;
    return serviceDispatchIn(&g_intf->s, p->cmd, in, .buffer_attrs = { attr }, .buffers = { { buf, size } });
}

/* Interface + endpoint descriptors for one speed. SuperSpeed adds an endpoint
 * companion after each endpoint. In blob mode they go in one call. */
static Result append_config(const usb_plan_t *p, UsbDeviceSpeed speed, mtp_descs_t *d, u16 bulk_mps)
{
    const bool ss = speed == UsbDeviceSpeed_Super;
    const struct { const void *p; size_t n; bool ss_only; } parts[] = {
        { &d->intf, USB_DT_INTERFACE_SIZE, false },
        { &d->in, USB_DT_ENDPOINT_SIZE, false },
        { &k_comp_bulk, USB_DT_SS_ENDPOINT_COMPANION_SIZE, true },
        { &d->out, USB_DT_ENDPOINT_SIZE, false },
        { &k_comp_bulk, USB_DT_SS_ENDPOINT_COMPANION_SIZE, true },
        { &d->irq, USB_DT_ENDPOINT_SIZE, false },
        { &k_comp_irq, USB_DT_SS_ENDPOINT_COMPANION_SIZE, true },
    };
    d->in.wMaxPacketSize = d->out.wMaxPacketSize = bulk_mps;

    if (p->blob) {
        u8 all[64];
        size_t n = 0;
        for (size_t i = 0; i < sizeof(parts) / sizeof(parts[0]); i++) {
            if (parts[i].ss_only && !ss) continue;
            memcpy(all + n, parts[i].p, parts[i].n);
            n += parts[i].n;
        }
        return append_raw(p, speed, all, n);
    }
    for (size_t i = 0; i < sizeof(parts) / sizeof(parts[0]); i++) {
        if (parts[i].ss_only && !ss) continue;
        Result rc = append_raw(p, speed, parts[i].p, parts[i].n);
        if (R_FAILED(rc)) return rc;
    }
    return 0;
}

static void fill_device_descriptor(struct usb_device_descriptor *dev, u8 iManufacturer, u8 iProduct, u8 iSerial)
{
    *dev = (struct usb_device_descriptor){
        .bLength            = USB_DT_DEVICE_SIZE,
        .bDescriptorType    = USB_DT_DEVICE,
        .bcdUSB             = 0x0200,
        .bDeviceClass       = 0x00,   /* class is defined per interface */
        .bDeviceSubClass    = 0x00,
        .bDeviceProtocol    = 0x00,
        .bMaxPacketSize0    = 0x40,
        .idVendor           = MTP_VID,
        .idProduct          = MTP_PID,
        .bcdDevice          = 0x0100,
        .iManufacturer      = iManufacturer,
        .iProduct           = iProduct,
        .iSerialNumber      = iSerial,
        .bNumConfigurations = 0x01,
    };
}

/* USB 2 High-Speed is required. Full-Speed (USB 1) and SuperSpeed (USB 3) are
 * extras: a speed whose descriptors usb:ds refuses is dropped from the plan
 * (and noted in the log) instead of failing the whole app. */
static int setup_device(usb_plan_t *p, bool quiet)
{
    static const u16 langs[] = { 0x0409 };   /* en-US */
    u8 iManufacturer, iProduct, iSerial, iInterface;
    struct usb_device_descriptor dev;
    char s[16];
    Result rc;

    TRY("language string", usbDsAddUsbLanguageStringDescriptor(NULL, langs, 1));
    TRY("string descriptors", usbDsAddUsbStringDescriptor(&iManufacturer, "Nintendo"));
    TRY("string descriptors", usbDsAddUsbStringDescriptor(&iProduct, "Nintendo Switch 2"));
    TRY("string descriptors", usbDsAddUsbStringDescriptor(&iSerial, g_serial));

    fill_device_descriptor(&dev, iManufacturer, iProduct, iSerial);
    TRY("USB 2 device descriptor", usbDsSetUsbDeviceDescriptor(UsbDeviceSpeed_High, &dev));
    if (p->full) {
        dev.bcdUSB = 0x0110;
        if (R_FAILED(rc = usbDsSetUsbDeviceDescriptor(UsbDeviceSpeed_Full, &dev))) {
            p->full = false;
            if (!quiet) { rc_short(s, sizeof(s), rc); status_log("USB: USB 1 descriptor refused (%s), skipped", s); }
        }
    }
    TRY("register interface", register_interface());
    TRY("string descriptors", usbDsAddUsbStringDescriptor(&iInterface, "MTP"));  /* Windows keys on this string */

    /* The SuperSpeed slot is registered last so its descriptor framing (and
     * the string replies served under it) is cached from the fully-registered
     * set: BOS + SS device descriptor applied after every string exists means
     * GET_DESCRIPTOR replies on the SS link are framed for the 512-byte SS
     * EP0. Registering SS earlier made Windows read the serial-number string
     * with High-Speed chunking and reject it truncated ("invalid serial
     * number string descriptor" -> Code 10). */
    if (p->super) {
        rc = usbDsSetBinaryObjectStore(k_bos, sizeof(k_bos));
        if (R_SUCCEEDED(rc)) {
            dev.bcdUSB = 0x0300;
            dev.bMaxPacketSize0 = 0x09;      /* 2^9 = 512 for SuperSpeed EP0 */
            rc = usbDsSetUsbDeviceDescriptor(UsbDeviceSpeed_Super, &dev);
        }
        if (R_FAILED(rc)) {
            p->super = false;
            if (!quiet) { rc_short(s, sizeof(s), rc); status_log("USB: USB 3 descriptor refused (%s), skipped", s); }
        }
    }

    mtp_descs_t d;
    fill_descs(&d, g_intf->interface_index, iInterface);
    if (p->full)  TRY("USB 1 configuration", append_config(p, UsbDeviceSpeed_Full, &d, 0x40));
    TRY("USB 2 configuration", append_config(p, UsbDeviceSpeed_High, &d, 0x200));
    if (p->super) TRY("USB 3 configuration", append_config(p, UsbDeviceSpeed_Super, &d, 0x400));

    bool ev;
    rc = register_endpoint(&g_ep_obj[0], d.in.bEndpointAddress, &ev);
    TRY(ev ? "bulk IN endpoint event" : "register bulk IN endpoint", rc);
    g_ep_in = &g_ep_obj[0];
    rc = register_endpoint(&g_ep_obj[1], d.out.bEndpointAddress, &ev);
    TRY(ev ? "bulk OUT endpoint event" : "register bulk OUT endpoint", rc);
    g_ep_out = &g_ep_obj[1];
    rc = register_endpoint(&g_ep_obj[2], d.irq.bEndpointAddress, &ev);
    TRY(ev ? "interrupt endpoint event" : "register interrupt endpoint", rc);
    g_ep_irq = &g_ep_obj[2];
    TRY("enable device", usbDsEnable());
    return TP_OK;
}

/* ---- probe: find the AppendConfigurationData form Switch 2 takes ----------------
 * Every attempt runs in its own session: usb:ds closes a session after a
 * request it doesn't accept, and nothing is enabled, so no host sees them. */

static Result probe_open(void)
{
    struct usb_device_descriptor dev;
    Result rc = usbDsInitialize();
    if (R_FAILED(rc)) return rc;
    fill_device_descriptor(&dev, 0, 0, 0);
    usbDsSetUsbDeviceDescriptor(UsbDeviceSpeed_High, &dev);
    dev.bcdUSB = 0x0110;
    usbDsSetUsbDeviceDescriptor(UsbDeviceSpeed_Full, &dev);
    usbDsSetBinaryObjectStore(k_bos, sizeof(k_bos));
    dev.bcdUSB = 0x0300;
    dev.bMaxPacketSize0 = 0x09;
    usbDsSetUsbDeviceDescriptor(UsbDeviceSpeed_Super, &dev);
    rc = register_interface();
    if (R_FAILED(rc)) usbDsExit();
    return rc;
}

static void probe_close(void)
{
    release_objects();
    usbDsExit();
}

/* The interface descriptor alone (or the whole set, in blob mode) at `speed`. */
static Result probe_append(const usb_plan_t *p, UsbDeviceSpeed speed)
{
    Result rc = probe_open();
    if (R_FAILED(rc)) return rc;
    mtp_descs_t d;
    fill_descs(&d, g_intf->interface_index, 0);
    u16 mps = speed == UsbDeviceSpeed_Super ? 0x400 : speed == UsbDeviceSpeed_Full ? 0x40 : 0x200;
    if (p->blob) {
        rc = append_config(p, speed, &d, mps);
    } else {
        d.in.wMaxPacketSize = d.out.wMaxPacketSize = mps;
        rc = append_raw(p, speed, &d.intf, USB_DT_INTERFACE_SIZE);
    }
    probe_close();
    return rc;
}

/* A command that takes nothing and returns one copy handle (an event getter). */
static Result probe_event_shape(u32 cmd)
{
    Result rc = probe_open();
    if (R_FAILED(rc)) return rc;
    Handle h = INVALID_HANDLE;
    serviceAssumeDomain(&g_intf->s);
    rc = serviceDispatch(&g_intf->s, cmd, .out_handle_attrs = { SfOutHandleAttr_HipcCopy }, .out_handles = &h);
    if (R_SUCCEEDED(rc) && h != INVALID_HANDLE) svcCloseHandle(h);
    probe_close();
    return rc;
}

/* With a working plan: the full High-Speed set, then the bulk IN endpoint. */
static void probe_endpoint(const usb_plan_t *p)
{
    char a[16], b[16];
    Result rc = probe_open();
    if (R_FAILED(rc)) return;
    mtp_descs_t d;
    fill_descs(&d, g_intf->interface_index, 0);
    rc = append_config(p, UsbDeviceSpeed_High, &d, 0x200);
    if (R_FAILED(rc)) {
        rc_short(a, sizeof(a), rc);
        status_log("probe: full USB 2 set with that form: %s", a);
    } else {
        bool ev;
        rc = register_endpoint(&g_ep_obj[0], d.in.bEndpointAddress, &ev);
        rc_short(a, sizeof(a), ev ? 0 : rc);
        if (ev) rc_short(b, sizeof(b), rc); else snprintf(b, sizeof(b), "-");
        status_log("probe endpoint: register %s, completion event %s", a, b);
    }
    probe_close();
}

/* Fills *out with the first configuration form that works for High-Speed,
 * with Full / Super enabled where they work too. Logs everything it tries. */
static bool probe(usb_plan_t *out)
{
    static const struct { buf_kind_t buf; bool pre11; } forms[] = {
        { BUF_MAP, false }, { BUF_AUTO, false }, { BUF_PTR, false }, { BUF_MAP, true },
    };
    char h[16], f[16], s[16], line[STATUS_LINE_LEN];
    bool have = false;

    /* 1. cmd 10 in each form, at each speed. */
    for (size_t i = 0; i < sizeof(forms) / sizeof(forms[0]); i++) {
        usb_plan_t p = { 10, forms[i].buf, forms[i].pre11, false, false, false };
        Result rh = probe_append(&p, UsbDeviceSpeed_High);
        Result rf = probe_append(&p, UsbDeviceSpeed_Full);
        Result rs = probe_append(&p, UsbDeviceSpeed_Super);
        rc_short(h, sizeof(h), rh); rc_short(f, sizeof(f), rf); rc_short(s, sizeof(s), rs);
        status_log("probe c10 %s%s: usb2 %s, usb1 %s, usb3 %s", buf_name(p.buf), p.pre11 ? "+pre11" : "", h, f, s);
        if (!have && R_SUCCEEDED(rh)) {
            *out = p;
            out->full = R_SUCCEEDED(rf);
            out->super = R_SUCCEEDED(rs);
            have = true;
        }
    }

    /* 2. The whole USB 2 set in one call. */
    {
        usb_plan_t p = k_libnx_plan;
        p.blob = true;
        p.full = p.super = false;
        Result rb = probe_append(&p, UsbDeviceSpeed_High);
        rc_short(h, sizeof(h), rb);
        status_log("probe c10 map, whole USB 2 set in one call: %s", h);
        if (!have && R_SUCCEEDED(rb)) {
            *out = p;
            out->full = R_SUCCEEDED(probe_append(&p, UsbDeviceSpeed_Full));
            out->super = R_SUCCEEDED(probe_append(&p, UsbDeviceSpeed_Super));
            have = true;
        }
    }

    /* 3. Every command 0-15 in libnx's AppendConfigurationData shape. */
    {
        char map[17] = {0};
        int first = -1;
        for (u32 cmd = 0; cmd < 16; cmd++) {
            usb_plan_t p = k_libnx_plan;
            p.cmd = cmd;
            Result rc = probe_append(&p, UsbDeviceSpeed_High);
            map[cmd] = rc_char(rc);
            /* 0 (RegisterEndpoint) and 1 (GetSetupEvent) are known to be other
             * commands on Switch 2; a lenient server could still accept this. */
            if (first < 0 && cmd > 1 && cmd != 10 && R_SUCCEEDED(rc)) first = (int)cmd;
        }
        snprintf(line, sizeof(line), "probe config shape, cmd 0-15: %s", map);
        status_log("%s", line);
        if (!have && first >= 0) {
            usb_plan_t p = k_libnx_plan;
            p.cmd = (u32)first;
            p.full = p.super = false;
            *out = p;
            out->full = R_SUCCEEDED(probe_append(&p, UsbDeviceSpeed_Full));
            out->super = R_SUCCEEDED(probe_append(&p, UsbDeviceSpeed_Super));
            have = true;
        }
    }

    /* 4. Every command 0-15 as an event getter (maps the interface's table). */
    {
        char map[17] = {0};
        for (u32 cmd = 0; cmd < 16; cmd++) map[cmd] = rc_char(probe_event_shape(cmd));
        status_log("probe event shape,  cmd 0-15: %s", map);
    }

    /* 5. Endpoints, with the form that works. */
    if (have) probe_endpoint(out);
    return have;
}

int tp_init(void)
{
    char s[16];
    g_fail_step = "";

    /* 1. The Switch 2 form (all speeds). Opens usb:ds through kaiHEN's SM
     *    proxy and binds this process. */
    usb_plan_t plan = k_switch2_plan;
    TRY("open usb:ds", usbDsInitialize());
    int r = setup_device(&plan, false);
    if (r == TP_OK) return TP_OK;
    release_objects();
    usbDsExit();
    if (strstr(g_fail_step, "configuration") == NULL) return r;

    rc_short(s, sizeof(s), g_last_rc);
    status_log("!! USB, Switch 2 form: %s %s", g_fail_step, s);

    /* 2. Find the form this console takes, then set up again with it. */
    usb_plan_t found;
    if (!probe(&found)) {
        status_log("!! USB: no configuration form worked (log above)");
        return TP_ERROR;
    }
    status_log("USB: retry with cmd %u %s%s%s, usb1 %s, usb3 %s", (unsigned)found.cmd, buf_name(found.buf),
               found.pre11 ? "+pre11" : "", found.blob ? " one-call" : "",
               found.full ? "on" : "off", found.super ? "on" : "off");
    TRY("open usb:ds", usbDsInitialize());
    r = setup_device(&found, true);
    if (r == TP_OK) {
        status_log("USB: setup OK");
        return TP_OK;
    }
    release_objects();
    usbDsExit();
    return r;
}

void tp_exit(void)
{
    tp_abort();
    release_objects();
    usbDsExit();   /* disables the device, detaches from the host */
}

int tp_is_configured(void)
{
    UsbState s;
    return R_SUCCEEDED(usbDsGetState(&s)) && s == UsbState_Configured;
}

static void refresh_speed(void)
{
    UsbDeviceSpeed sp;
    if (R_FAILED(usbDsGetSpeed(&sp))) { g_mps = 512; return; }
    g_mps = sp == UsbDeviceSpeed_Super ? 1024 : sp == UsbDeviceSpeed_Full ? 64 : 512;
}

int tp_wait_configured(uint32_t timeout_ms)
{
    u64 waited = 0, limit = (u64)timeout_ms * 1000000ull;
    for (;;) {
        if (stopping()) return TP_STOPPED;
        if (tp_is_configured()) { refresh_speed(); return TP_OK; }
        if (timeout_ms && waited >= limit) return TP_TIMEOUT;
        Event *ev = usbDsGetStateChangeEvent();
        if (R_SUCCEEDED(eventWait(ev, WAIT_SLICE_NS))) eventClear(ev);
        waited += WAIT_SLICE_NS;
    }
}

uint32_t tp_max_packet(void) { return g_mps; }

/* Cancels the URB on `ep` and waits (bounded) for its completion so the
 * buffer is no longer owned by the controller when we return. */
static void cancel_ep(UsbDsEndpoint *ep, bool *posted)
{
    if (!*posted || !ep) return;
    usbDsEndpoint_Cancel(ep);
    eventWait(&ep->CompletionEvent, 500000000ull);
    eventClear(&ep->CompletionEvent);
    *posted = false;
}

void tp_abort(void)
{
    cancel_ep(g_ep_out, &g_rd_posted);
    cancel_ep(g_ep_in, &g_wr_posted);
}

static int post(UsbDsEndpoint *ep, const void *buf, uint32_t size, u32 *urb, bool *posted)
{
    if (!tp_is_configured()) return TP_DISCONNECTED;
    /* usb:ds DMA needs page-aligned buffers; the cast drops const because
     * PostBufferAsync is used for both directions. */
    Result rc = usbDsEndpoint_PostBufferAsync(ep, (void *)buf, size, urb);
    if (R_FAILED(rc)) { g_last_rc = rc; return tp_is_configured() ? TP_ERROR : TP_DISCONNECTED; }
    *posted = true;
    return TP_OK;
}

static int complete(UsbDsEndpoint *ep, u32 urb, bool *posted, uint32_t *transferred, uint32_t timeout_ms)
{
    u64 waited = 0, limit = (u64)timeout_ms * 1000000ull;
    *transferred = 0;
    for (;;) {
        if (R_SUCCEEDED(eventWait(&ep->CompletionEvent, WAIT_SLICE_NS))) break;
        waited += WAIT_SLICE_NS;
        int why = stopping() ? TP_STOPPED
                : !tp_is_configured() ? TP_DISCONNECTED
                : (timeout_ms && waited >= limit) ? TP_TIMEOUT : TP_OK;
        if (why != TP_OK) { cancel_ep(ep, posted); return why; }
    }
    eventClear(&ep->CompletionEvent);
    *posted = false;

    UsbDsReportData rep;
    u32 got = 0;
    Result rc = usbDsEndpoint_GetReportData(ep, &rep);
    if (R_SUCCEEDED(rc)) rc = usbDsParseReportData(&rep, urb, NULL, &got);
    if (R_FAILED(rc)) { g_last_rc = rc; return tp_is_configured() ? TP_ERROR : TP_DISCONNECTED; }
    *transferred = got;
    return TP_OK;
}

int tp_read_begin(void *buf, uint32_t size)            { return post(g_ep_out, buf, size, &g_rd_urb, &g_rd_posted); }
int tp_write_begin(const void *buf, uint32_t size)     { return post(g_ep_in, buf, size, &g_wr_urb, &g_wr_posted); }
int tp_read_end(uint32_t *n, uint32_t timeout_ms)      { return complete(g_ep_out, g_rd_urb, &g_rd_posted, n, timeout_ms); }
int tp_write_end(uint32_t *n, uint32_t timeout_ms)     { return complete(g_ep_in, g_wr_urb, &g_wr_posted, n, timeout_ms); }
