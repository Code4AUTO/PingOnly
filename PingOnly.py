# ping_only_app.py
import os
import sys
import json
import time
import math
import queue
import shutil
import logging
import platform
import subprocess
import ipaddress
from pathlib import Path
from collections import deque
from threading import Event, Lock, Thread
from concurrent.futures import ThreadPoolExecutor, as_completed, wait
import re
from typing import Optional, Tuple, List, Any, Dict

import tkinter as tk
from tkinter import ttk, messagebox, simpledialog, filedialog

# ===================== 配置默认值 =====================
APP_NAME = "PingOnly"
DEFAULT_PING_INTERVAL = 3            # 秒
DEFAULT_FAIL_THRESHOLD = 3
DEFAULT_PING_TIMEOUT_MS = 2000      # ms
DEFAULT_LOG_FILENAME = "log.txt"
DEFAULT_HOSTS_FILENAME = "hosts.json"
MAX_CHART_POINTS = 100
DEFAULT_Y_MAX = 100
DEFAULT_MAX_WORKERS = 50            # 线程池并发数上限（初始默认，会根据 CPU/hosts 调整）
UI_TREE_THROTTLE_SEC = 0.5          # 刷新树/图表的最小时隔
SAVE_RECENT_COUNT = 20              # 保存到 hosts.json 的最近 RTT 数量
SHUTDOWN_WAIT_FUTURES = 3.0         # 退出时等待在飞 futures 的秒数
MAX_LOG_LINES_LOAD = 1000           # 初次加载进 UI 的最大日志行数

# ===================== module logger =====================
logger = logging.getLogger(__name__)

# ===================== ping3 optional backend =====================
try:
    import ping3  # type: ignore
    HAVE_PING3 = True
except Exception:
    HAVE_PING3 = False

# ===================== 多模式解析 PATTERNS =====================
PATTERNS = [
    re.compile(r"time[=<]\s*([<\d.]+)\s*ms", re.IGNORECASE),        # common english: time=1.23ms, time<1ms
    re.compile(r"时间[=<]\s*([<\d.]+)\s*毫秒", re.IGNORECASE),        # chinese: 时间=1ms
    re.compile(r"ttl=\d+\s+time[=<]\s*([<\d.]+)", re.IGNORECASE),    # another variation
    # Add more patterns if needed
]


# ===================== 辅助函数 =====================
def get_app_dir() -> str:
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))


def valid_host(host: str) -> bool:
    """
    支持 IPv4 / IPv6 / hostname 简单校验
    """
    host = host.strip()
    if not host:
        return False
    # try ipaddress for IPv4/IPv6
    try:
        ipaddress.ip_address(host)
        return True
    except Exception:
        pass
    # Hostname/domain (simple)
    hostname_re = re.compile(r"^(?!-)[A-Za-z0-9-]{1,63}(?<!-)(\.[A-Za-z0-9-]{1,63})*$")
    return bool(hostname_re.match(host))


# ===================== 主类 =====================
class PingOnlyApp:
    def __init__(
        self,
        app_dir: Optional[str] = None,
        log_filename: str = DEFAULT_LOG_FILENAME,
        hosts_filename: str = DEFAULT_HOSTS_FILENAME,
        ping_interval: int = DEFAULT_PING_INTERVAL,
        fail_threshold: int = DEFAULT_FAIL_THRESHOLD,
        max_workers: Optional[int] = None,
        ping_timeout_ms: int = DEFAULT_PING_TIMEOUT_MS,
    ):
        # paths & config
        self.app_dir = app_dir or get_app_dir()
        self.log_file = os.path.join(self.app_dir, log_filename)
        self.hosts_file = os.path.join(self.app_dir, hosts_filename)
        self.ping_interval = max(1, int(ping_interval))
        self.fail_threshold = max(1, int(fail_threshold))
        self.ping_timeout_ms = max(500, int(ping_timeout_ms))
        self.max_workers = max(1, int(max_workers)) if max_workers else None

        # shared state
        self.ip_list: List[str] = []
        self.host_status: Dict[str, str] = {}         # ip -> "Waiting"/"Good"/"Bad"
        self.fail_count: Dict[str, int] = {}          # ip -> int
        self.delay_data: Dict[str, deque] = {}        # ip -> deque
        self.data_lock = Lock()

        # UI & threading
        self.ui_queue = queue.Queue()
        self.stop_event = Event()
        self.executor: Optional[ThreadPoolExecutor] = None
        self._executor_lock = Lock()
        self.monitor_thread: Optional[Thread] = None

        # futures tracking for graceful shutdown
        self._futures = set()
        self._futures_lock = Lock()

        # UI widgets (assigned in build_ui)
        self.root: Optional[tk.Tk] = None
        self.host_tree: Optional[ttk.Treeview] = None
        self.chart_canvas: Optional[tk.Canvas] = None
        self.log_text_widget: Optional[tk.Text] = None
        self.input_entry: Optional[tk.Entry] = None
        self.right_click_menu: Optional[tk.Menu] = None

        # chart drawing reuse
        self._chart_line_id: Optional[int] = None
        self._chart_point_ids: List[int] = []

        # UI throttles
        self._last_tree_refresh = 0.0
        self._pending_tree_refresh = False

        # prepare logging
        self._init_logger()
        logger.info("PingOnlyApp initialized (ping_interval=%ds, ping_timeout_ms=%d, fail_threshold=%d, max_workers=%s)",
                    self.ping_interval, self.ping_timeout_ms, self.fail_threshold, str(self.max_workers))

        # load hosts (and compute smart default workers)
        self.load_hosts()
        self._adjust_default_workers()

    # ---------------- logging ----------------
    def _init_logger(self):
        os.makedirs(self.app_dir, exist_ok=True)
        logger.setLevel(logging.INFO)
        fmt = logging.Formatter("%(asctime)s | %(message)s", "%Y-%m-%d %H:%M:%S")
        # Avoid adding multiple handlers if re-instantiated
        if not logger.handlers:
            try:
                from logging.handlers import RotatingFileHandler
                fh = RotatingFileHandler(self.log_file, maxBytes=5 * 1024 * 1024, backupCount=3, encoding="utf-8")
                fh.setFormatter(fmt)
                logger.addHandler(fh)
            except Exception:
                ch = logging.StreamHandler()
                ch.setFormatter(fmt)
                logger.addHandler(ch)

    def write_log(self, msg: str):
        # logging will add timestamp via handler; UI shows our formatted line
        line = f"{time.strftime('%Y-%m-%d %H:%M:%S')} | {msg}"
        try:
            logger.info(msg)
        except Exception:
            print(line)
        self.ui_queue.put(("log", line))

    def _load_logs_into_ui(self, max_lines: int = MAX_LOG_LINES_LOAD):
        """
        Read last max_lines from the log file and insert into the UI log widget.
        Call this after log_text_widget exists.
        """
        if not self.log_text_widget:
            return
        if not os.path.exists(self.log_file):
            return
        try:
            # Efficient tail: read lines into deque
            with open(self.log_file, "r", encoding="utf-8", errors="replace") as f:
                dq = deque(f, maxlen=max_lines)
            for line in dq:
                self.log_text_widget.insert(tk.END, line.rstrip("\n") + "\n")
            self.log_text_widget.see(tk.END)
        except Exception:
            logger.exception("Failed to load log file into UI")

    # ---------------- persistence (richer format + backup on corrupt) ----------------
    def load_hosts(self):
        self.ip_list = []
        self.host_status = {}
        self.fail_count = {}
        self.delay_data = {}
        if os.path.exists(self.hosts_file):
            try:
                with open(self.hosts_file, "r", encoding="utf-8") as f:
                    raw = json.load(f)
                # support richer format
                loaded_ips = []
                if isinstance(raw, dict) and "hosts" in raw:
                    for h in raw["hosts"]:
                        ip = h.get("ip")
                        if ip:
                            loaded_ips.append(ip)
                            status = h.get("status", "Waiting")
                            recent = h.get("recent", [])
                            self.host_status[ip] = status
                            self.fail_count[ip] = 0
                            dq = deque(maxlen=MAX_CHART_POINTS)
                            for v in recent[-MAX_CHART_POINTS:]:
                                dq.append(v)
                            self.delay_data[ip] = dq
                elif isinstance(raw, dict) and "ips" in raw:
                    loaded_ips = raw["ips"]
                elif isinstance(raw, list):
                    loaded_ips = raw
                for ip in loaded_ips:
                    if ip not in self.host_status:
                        self.host_status[ip] = "Waiting"
                        self.fail_count[ip] = 0
                        self.delay_data[ip] = deque(maxlen=MAX_CHART_POINTS)
                self.ip_list = loaded_ips
                logger.info("Loaded %d hosts from %s", len(self.ip_list), self.hosts_file)
            except Exception:
                # backup corrupt file
                try:
                    import datetime
                    ts = datetime.datetime.now().strftime("%Y%m%d%H%M%S")
                    corrupt_name = f"{self.hosts_file}.corrupt.{ts}"
                    os.replace(self.hosts_file, corrupt_name)
                    logger.exception("hosts.json corrupt; moved to %s", corrupt_name)
                except Exception:
                    logger.exception("hosts.json corrupt and backup failed")
                self.ip_list = []
        else:
            logger.info("No hosts.json found at %s; starting empty", self.hosts_file)

    def save_hosts(self):
        try:
            payload = []
            with self.data_lock:
                for ip in self.ip_list:
                    recent = list(self.delay_data.get(ip, []))[-SAVE_RECENT_COUNT:]
                    payload.append({
                        "ip": ip,
                        "status": self.host_status.get(ip, "Waiting"),
                        "recent": recent
                    })
            tmp = self.hosts_file + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump({"hosts": payload}, f, indent=2, ensure_ascii=False)
            os.replace(tmp, self.hosts_file)
            logger.info("Saved hosts (%d) to %s", len(self.ip_list), self.hosts_file)
        except Exception:
            logger.exception("Failed to save hosts.json")

    # ---------------- smart default workers ----------------
    def _adjust_default_workers(self):
        # If max_workers was not explicitly set, choose a reasonable default based on CPU & host count
        if self.max_workers is None:
            cpu = os.cpu_count() or 2
            host_count = max(1, len(self.ip_list))
            # heuristic: 2 * cpus, but no more than DEFAULT_MAX_WORKERS, and not more than host_count
            suggested = min(DEFAULT_MAX_WORKERS, max(4, cpu * 2, min(host_count, DEFAULT_MAX_WORKERS)))
            # cap to reasonable upper bound
            suggested = min(suggested, 200)
            self.max_workers = max(4, suggested)
            logger.info("Auto-selected max_workers=%d (cpu=%d, hosts=%d)", self.max_workers, cpu, host_count)

    # ---------------- ping implementation (ping3 optional) ----------------
    def _ping_ip_ping3(self, ip: str, timeout_ms: int = DEFAULT_PING_TIMEOUT_MS) -> Tuple[bool, Optional[int]]:
        """Use ping3 backend if available. Returns (online, delay_ms|None)"""
        try:
            r = ping3.ping(ip, timeout=timeout_ms / 1000.0)  # type: ignore
            if r is None:
                return False, None
            else:
                return True, int(round(r * 1000))
        except Exception:
            logger.debug("ping3 backend exception for %s", ip, exc_info=True)
            return False, None

    def _ping_ip_subprocess(self, ip: str, timeout_ms: int = DEFAULT_PING_TIMEOUT_MS) -> Tuple[bool, Optional[int]]:
        ping_exe = shutil.which("ping")
        if not ping_exe:
            logger.debug("ping not found on system")
            return False, None

        sys_name = platform.system()
        timeout_sec = timeout_ms / 1000.0
        proc_timeout = timeout_sec + 1.0

        if sys_name == "Windows":
            cmd = [ping_exe, "-n", "1", "-w", str(int(timeout_ms)), ip]
            creationflags = getattr(subprocess, "CREATE_NO_WINDOW", 0x08000000)
            sub_args = {"args": cmd, "capture_output": True, "text": True, "timeout": proc_timeout,
                        "creationflags": creationflags}
        elif sys_name == "Linux":
            timeout_s = max(1, int(math.ceil(timeout_sec)))
            cmd = [ping_exe, "-c", "1", "-W", str(timeout_s), ip]
            sub_args = {"args": cmd, "capture_output": True, "text": True, "timeout": proc_timeout}
        elif sys_name == "Darwin":
            cmd = [ping_exe, "-c", "1", ip]
            sub_args = {"args": cmd, "capture_output": True, "text": True, "timeout": proc_timeout}
        else:
            cmd = [ping_exe, "-c", "1", ip]
            sub_args = {"args": cmd, "capture_output": True, "text": True, "timeout": proc_timeout}

        try:
            res = subprocess.run(**sub_args)
        except subprocess.TimeoutExpired:
            logger.debug("ping subprocess timeout for %s", ip)
            return False, None
        except FileNotFoundError:
            logger.debug("ping executable missing (FileNotFound) for %s", ip)
            return False, None
        except Exception:
            logger.exception("Unexpected exception running ping for %s", ip)
            return False, None

        out = (res.stdout or "") + "\n" + (res.stderr or "")
        delay = None
        for line in out.splitlines():
            for pat in PATTERNS:
                m = pat.search(line)
                if m:
                    val_str = m.group(1)
                    if val_str.startswith("<"):
                        try:
                            delay = max(1, int(math.ceil(float(val_str.lstrip("<")))))
                        except Exception:
                            delay = 1
                    else:
                        try:
                            delay = int(round(float(val_str)))
                        except Exception:
                            delay = None
                    break
            if delay is not None:
                break

        online = (res.returncode == 0)
        return online, delay

    def _ping_ip(self, ip: str, timeout_ms: int = None) -> Tuple[bool, Optional[int]]:
        timeout_ms = timeout_ms if timeout_ms is not None else self.ping_timeout_ms
        # Try ping3 first if available
        if HAVE_PING3:
            online, delay = self._ping_ip_ping3(ip, timeout_ms)
            if online or delay is not None:
                return online, delay
        return self._ping_ip_subprocess(ip, timeout_ms)

    # ---------------- single ping task handler (for executor) ----------------
    def _future_done_cb(self, fut):
        with self._futures_lock:
            self._futures.discard(fut)

    def _do_ping_once(self, ip: str) -> None:
        """Called inside executor worker - run one ping and update shared state."""
        online, delay = self._ping_ip(ip, timeout_ms=self.ping_timeout_ms)
        with self.data_lock:
            if ip not in self.delay_data:
                self.delay_data[ip] = deque(maxlen=MAX_CHART_POINTS)
            self.delay_data[ip].append(delay)

            if not online:
                self.fail_count[ip] = self.fail_count.get(ip, 0) + 1
                if self.fail_count[ip] >= self.fail_threshold and self.host_status.get(ip) != "Bad":
                    self.host_status[ip] = "Bad"
                    self.write_log(f"[Offline] Host {ip} offline, status set to Bad")
            else:
                self.fail_count[ip] = 0
                if self.host_status.get(ip) != "Good":
                    self.host_status[ip] = "Good"
                    self.write_log(f"[Recover] Host {ip} connected, status set to Good")
        # request UI refresh (throttled)
        self._enqueue_tree_refresh()

    # ---------------- UI refresh enqueue (throttled consumption later) ----------------
    def _enqueue_tree_refresh(self):
        self._pending_tree_refresh = True
        self.ui_queue.put(("refresh_tree", None))

    # ---------------- monitor loop: schedule ping tasks periodically (precise scheduling) ----------------
    def _monitor_loop(self):
        logger.info("Monitor loop started")
        next_run = time.monotonic()
        try:
            while not self.stop_event.is_set():
                start = time.monotonic()
                with self.data_lock:
                    ips = list(self.ip_list)
                if ips:
                    if len(ips) > (self.max_workers * 4):
                        self.write_log(f"[Performance] Host count ({len(ips)}) >> max_workers ({self.max_workers}). Consider increasing interval or workers.")
                    futures = []
                    with self._executor_lock:
                        exec_ref = self.executor
                    if not exec_ref:
                        self.stop_event.wait(self.ping_interval)
                    else:
                        for ip in ips:
                            try:
                                f = exec_ref.submit(self._do_ping_once, ip)
                            except Exception:
                                logger.exception("Failed to submit ping task for %s", ip)
                                continue
                            with self._futures_lock:
                                self._futures.add(f)
                            f.add_done_callback(self._future_done_cb)
                            futures.append(f)
                        # wait up to ping_interval for tasks to finish
                        try:
                            start_wait = time.monotonic()
                            for f in as_completed(futures, timeout=self.ping_interval):
                                if self.stop_event.is_set():
                                    break
                                if time.monotonic() - start_wait > self.ping_interval:
                                    break
                        except Exception:
                            pass
                # schedule next run time precisely
                next_run += self.ping_interval
                sleep = max(0, next_run - time.monotonic())
                # If next_run was in the past (e.g., long task), reset next_run to now
                if sleep == 0 and time.monotonic() - start > self.ping_interval:
                    next_run = time.monotonic()
                    sleep = self.ping_interval
                self.stop_event.wait(sleep)
        finally:
            logger.info("Monitor loop exiting")

    # ---------------- executor management (allow runtime replacement) ----------------
    def _create_executor(self):
        with self._executor_lock:
            # shutdown existing executor if any
            if self.executor:
                try:
                    self.executor.shutdown(wait=False)
                except Exception:
                    logger.exception("Error shutting down existing executor during recreate")
                self.executor = None
            # create new one
            try:
                self.executor = ThreadPoolExecutor(max_workers=self.max_workers)
                logger.info("Created ThreadPoolExecutor with max_workers=%d", self.max_workers)
            except Exception:
                logger.exception("Failed to create ThreadPoolExecutor")
                self.executor = None

    # ---------------- UI build and helpers ----------------
    def build_ui(self):
        self.root = tk.Tk()
        self.root.title(APP_NAME)
        self.root.geometry("1200x750")
        self.root.protocol("WM_DELETE_WINDOW", self._on_window_close)

        # menu: Settings + IO + Help (Help after IO)
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)

        settings_menu = tk.Menu(menubar, tearoff=0)
        settings_menu.add_command(label="Settings...", command=self._show_settings)
        menubar.add_cascade(label="Settings", menu=settings_menu)

        io_menu = tk.Menu(menubar, tearoff=0)
        io_menu.add_command(label="Import hosts...", command=self._import_hosts)
        io_menu.add_command(label="Export hosts...", command=self._export_hosts)
        menubar.add_cascade(label="IO", menu=io_menu)

        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="About", command=self._show_about)
        menubar.add_cascade(label="Help", menu=help_menu)

        # Top controls
        top_frame = tk.Frame(self.root)
        top_frame.pack(fill=tk.X, padx=8, pady=6)
        self.input_entry = tk.Entry(top_frame, width=28)
        self.input_entry.pack(side=tk.LEFT)
        tk.Button(top_frame, text="Add a host", command=self._on_add_host).pack(side=tk.LEFT, padx=5)

        # Main layout
        main_frame = tk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

        # Left: host list
        left_frame = tk.Frame(main_frame, width=260)
        left_frame.pack(side=tk.LEFT, fill=tk.BOTH, padx=(0, 8))
        self.host_tree = ttk.Treeview(left_frame, columns=("ip", "state"), show="headings")
        self.host_tree.heading("ip", text="Host")
        self.host_tree.heading("state", text="Status")
        self.host_tree.column("ip", width=160)
        self.host_tree.column("state", width=70)
        self.host_tree.pack(fill=tk.BOTH, expand=True)
        self.host_tree.tag_configure("good", foreground="#009900")
        self.host_tree.tag_configure("bad", foreground="#ff2222")
        self.host_tree.tag_configure("waiting", foreground="#666666")
        self.host_tree.bind("<<TreeviewSelect>>", self._on_left_click_host)
        self.host_tree.bind("<Button-3>", self._show_right_menu)
        self.host_tree.bind("<Control-Button-1>", self._show_right_menu)

        # right-click menu
        self.right_click_menu = tk.Menu(self.root, tearoff=0)
        self.right_click_menu.add_command(label="Edit Host", command=self._menu_edit_host)
        self.right_click_menu.add_command(label="Delete Host", command=self._menu_del_host)

        # Right: chart and log
        right_frame = tk.Frame(main_frame)
        right_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        chart_frame = tk.LabelFrame(right_frame, text="Round-Trip Time")
        chart_frame.pack(fill=tk.BOTH, expand=True)
        self.chart_canvas = tk.Canvas(chart_frame, bg="white")
        self.chart_canvas.pack(fill=tk.BOTH, expand=True)

        log_frame = tk.LabelFrame(right_frame, text="Log")
        log_frame.pack(fill=tk.X, pady=(6, 0))
        self.log_text_widget = tk.Text(log_frame, height=12)
        self.log_text_widget.pack(fill=tk.BOTH, expand=True)

        # Load existing log file content into UI so history is preserved across restarts
        self._load_logs_into_ui(max_lines=MAX_LOG_LINES_LOAD)

        # schedule periodic tasks / start monitor
        self.root.after(200, self._start_monitor)
        self.root.after(300, self._draw_chart)
        self.root.after(1000, self._auto_refresh_chart)
        self.root.after(100, self._check_ui_queue)

        # initial populate
        self.refresh_host_tree()

    def run(self):
        self.build_ui()
        self.root.mainloop()

    # ---------------- monitor & lifecycle (more reliable shutdown) ----------------
    def _start_monitor(self):
        # check ping availability and warn if missing
        if HAVE_PING3:
            logger.info("Using ping3 backend")
        else:
            if shutil.which("ping") is None:
                self.write_log("Warning: system 'ping' not found; reachability checks will fail.")
                messagebox.showwarning("Ping not found", "System 'ping' executable not found. The app will still run but cannot perform ping checks.")
        # create executor
        self._create_executor()
        # start monitor thread
        self.stop_event.clear()
        self.monitor_thread = Thread(target=self._monitor_loop, daemon=True)
        self.monitor_thread.start()
        self.write_log("[System] Monitor started")

    def _stop_monitor(self):
        self.write_log("[System] Stopping monitor...")
        self.stop_event.set()
        # join monitor thread
        if self.monitor_thread and self.monitor_thread.is_alive():
            self.monitor_thread.join(timeout=3)
        # gather pending futures and wait for them to complete up to SHUTDOWN_WAIT_FUTURES
        with self._futures_lock:
            pending = {f for f in self._futures if not f.done()}
        if pending:
            try:
                logger.info("Waiting for %d in-flight tasks to complete (up to %.1fs)", len(pending), SHUTDOWN_WAIT_FUTURES)
                done, not_done = wait(pending, timeout=SHUTDOWN_WAIT_FUTURES)
                if not_done:
                    logger.info("Some tasks did not finish within timeout (%d tasks)", len(not_done))
            except Exception:
                logger.exception("Error while waiting for futures during shutdown")
        # finally shutdown executor
        with self._executor_lock:
            if self.executor:
                try:
                    self.executor.shutdown(wait=False)
                except Exception:
                    logger.exception("Error shutting down executor")
                self.executor = None

    def _on_window_close(self):
        # graceful shutdown
        self._stop_monitor()
        self.write_log("[System] Shutting down application")
        self.save_hosts()
        try:
            if self.root:
                self.root.destroy()
        except Exception:
            pass

    # ---------------- UI interaction functions ----------------
    def refresh_host_tree(self):
        if not self.host_tree:
            return
        sel = self.host_tree.selection()
        sel_ip = ""
        if sel:
            sel_ip = self.host_tree.item(sel[0])["values"][0]
        # clear
        for item in self.host_tree.get_children():
            self.host_tree.delete(item)
        with self.data_lock:
            for ip in self.ip_list:
                state = self.host_status.get(ip, "Waiting")
                item_id = self.host_tree.insert("", tk.END, values=(ip, state))
                if state == "Good":
                    self.host_tree.item(item_id, tags=("good",))
                elif state == "Bad":
                    self.host_tree.item(item_id, tags=("bad",))
                else:
                    self.host_tree.item(item_id, tags=("waiting",))
        # restore selection
        if sel_ip and sel_ip in self.ip_list:
            try:
                idx = self.ip_list.index(sel_ip)
                self.host_tree.selection_set(self.host_tree.get_children()[idx])
            except Exception:
                pass

    def _enqueue_ui_refresh_if_allowed(self):
        now = time.time()
        if now - self._last_tree_refresh >= UI_TREE_THROTTLE_SEC:
            self.ui_queue.put(("refresh_tree", None))
            self._last_tree_refresh = now
            self._pending_tree_refresh = False
        else:
            self._pending_tree_refresh = True

    def _check_ui_queue(self):
        """Consume ui queue: logs and (throttled) refresh events."""
        processed_refresh = False
        while True:
            try:
                task, payload = self.ui_queue.get_nowait()
            except queue.Empty:
                break
            if task == "log":
                if self.log_text_widget:
                    self.log_text_widget.insert(tk.END, payload + "\n")
                    self.log_text_widget.see(tk.END)
            elif task == "refresh_tree":
                processed_refresh = True
        # throttle refreshes
        if processed_refresh:
            self._enqueue_ui_refresh_if_allowed()
        # if pending and enough time passed, flush
        if self._pending_tree_refresh:
            now = time.time()
            if now - self._last_tree_refresh >= UI_TREE_THROTTLE_SEC:
                self.refresh_host_tree()
                self._last_tree_refresh = now
                self._pending_tree_refresh = False
        # schedule next check
        if self.root:
            self.root.after(100, self._check_ui_queue)

    # ---------------- host add/edit/delete ----------------
    def _on_add_host(self):
        ip = (self.input_entry.get().strip() if self.input_entry else "").strip()
        if not ip:
            messagebox.showwarning("Warning", "IP cannot be empty")
            return
        if not valid_host(ip):
            messagebox.showwarning("Warning", "Input doesn't look like a valid IP/hostname")
            return
        with self.data_lock:
            if ip in self.ip_list:
                messagebox.showinfo("Info", "Host already exists")
                return
            self.ip_list.append(ip)
            self.host_status[ip] = "Waiting"
            self.fail_count[ip] = 0
            self.delay_data[ip] = deque(maxlen=MAX_CHART_POINTS)
        self.write_log(f"[Add Host] {ip}")
        self.save_hosts()
        self.refresh_host_tree()
        if self.input_entry:
            self.input_entry.delete(0, tk.END)

    def _show_right_menu(self, event):
        sel = self.host_tree.selection()
        if not sel:
            return
        self.host_tree.focus(sel[0])
        try:
            self.right_click_menu.post(event.x_root, event.y_root)
        except Exception:
            pass

    def _menu_edit_host(self):
        sel = self.host_tree.selection()
        if not sel:
            return
        item = self.host_tree.item(sel[0])
        old = item["values"][0]
        new = simpledialog.askstring("Edit Host", "Input new IP / domain:", initialvalue=old)
        if not new:
            return
        new = new.strip()
        if new == old:
            return
        if not valid_host(new):
            messagebox.showwarning("Warning", "Input doesn't look like a valid IP/hostname")
            return
        with self.data_lock:
            if new in self.ip_list:
                messagebox.showinfo("Info", "Host already exists")
                return
            try:
                idx = self.ip_list.index(old)
            except ValueError:
                return
            self.ip_list[idx] = new
            # clean old metadata
            self.host_status.pop(old, None)
            self.fail_count.pop(old, None)
            self.delay_data.pop(old, None)
            self.host_status[new] = "Waiting"
            self.fail_count[new] = 0
            self.delay_data[new] = deque(maxlen=MAX_CHART_POINTS)
        self.write_log(f"[Edit Host] {old} -> {new}")
        self.save_hosts()
        self.refresh_host_tree()
        self._draw_chart()

    def _menu_del_host(self):
        sel = self.host_tree.selection()
        if not sel:
            return
        item = self.host_tree.item(sel[0])
        ip = item["values"][0]
        with self.data_lock:
            try:
                self.ip_list.remove(ip)
            except ValueError:
                pass
            self.host_status.pop(ip, None)
            self.fail_count.pop(ip, None)
            self.delay_data.pop(ip, None)
        self.write_log(f"[Delete Host] {ip}")
        self.save_hosts()
        self.refresh_host_tree()
        self._draw_chart()

    def _on_left_click_host(self, _event):
        self._draw_chart()

    # ---------------- chart drawing (reuse items) ----------------
    def _draw_chart(self):
        if self.chart_canvas is None:
            return
        self.chart_canvas.update_idletasks()
        w = self.chart_canvas.winfo_width()
        h = self.chart_canvas.winfo_height()
        pad = 55
        chart_w = max(10, w - pad * 2)
        chart_h = max(10, h - pad * 2)

        # axes: clear only axes area by deleting tag "axes"
        self.chart_canvas.delete("axes")
        self.chart_canvas.create_line(pad, pad, pad, h - pad, fill="#222222", width=2, tags=("axes",))
        self.chart_canvas.create_line(pad, h - pad, w - pad, h - pad, fill="#222222", width=2, tags=("axes",))

        sel = self.host_tree.selection()
        if not sel:
            self.chart_canvas.delete("plot")
            self.chart_canvas.create_text(w / 2, h / 2, text="Left-click host on left to view RTT curve", fill="#666666", tags=("axes",))
            return
        ip = self.host_tree.item(sel[0])["values"][0]
        with self.data_lock:
            data = list(self.delay_data.get(ip, []))
        if not data:
            self.chart_canvas.delete("plot")
            self.chart_canvas.create_text(w / 2, h / 2, text="No data yet", fill="#666666", tags=("axes",))
            return
        n = len(data)
        if n < 2:
            self.chart_canvas.delete("plot")
            self.chart_canvas.create_text(w / 2, h / 2, text=f"Collecting data, {n} samples collected", fill="#666666", tags=("axes",))
            return

        valid = [d for d in data if d is not None]
        max_delay = max(valid) if valid else DEFAULT_Y_MAX
        max_delay = max(max_delay, DEFAULT_Y_MAX)

        # x spacing across n-1 intervals
        x_step = chart_w / (n - 1) if n > 1 else 0

        # dynamic y ticks
        y_ticks = [0, max_delay / 3.0, (2 * max_delay) / 3.0, max_delay]
        for tick in y_ticks:
            ratio = tick / max_delay if max_delay > 0 else 0
            y_pos = h - pad - ratio * chart_h
            self.chart_canvas.create_line(pad - 8, y_pos, pad, y_pos, fill="#222", width=1.5, tags=("axes",))
            self.chart_canvas.create_text(pad - 12, y_pos, text=f"{int(tick)}ms", anchor="e", font=("TkDefaultFont", 10), tags=("axes",))
            self.chart_canvas.create_line(pad, y_pos, w - pad, y_pos, fill="#dddddd", dash=(2, 2), tags=("axes",))

        coords = []
        for idx, v in enumerate(data):
            x = pad + idx * x_step
            if v is None:
                y = h - pad
            else:
                ratio = v / max_delay if max_delay > 0 else 0
                y = h - pad - ratio * chart_h
            coords.extend((x, y))

        # plot polyline: create or update
        if self._chart_line_id is None:
            try:
                self._chart_line_id = self.chart_canvas.create_line(*coords, fill="#0077dd", width=2, tags=("plot",))
            except Exception:
                self._chart_line_id = None
        else:
            try:
                self.chart_canvas.coords(self._chart_line_id, *coords)
            except Exception:
                try:
                    self.chart_canvas.delete(self._chart_line_id)
                except Exception:
                    pass
                self._chart_line_id = self.chart_canvas.create_line(*coords, fill="#0077dd", width=2, tags=("plot",))

        # points (ovals): ensure _chart_point_ids length equals n
        r = 4
        for i in range(n):
            x = coords[2 * i]
            y = coords[2 * i + 1]
            if i < len(self._chart_point_ids):
                oid = self._chart_point_ids[i]
                try:
                    self.chart_canvas.coords(oid, x - r, y - r, x + r, y + r)
                except Exception:
                    try:
                        self.chart_canvas.delete(oid)
                    except Exception:
                        pass
                    oid = self.chart_canvas.create_oval(x - r, y - r, x + r, y + r, fill="#0077dd", tags=("plot",))
                    self._chart_point_ids[i] = oid
            else:
                oid = self.chart_canvas.create_oval(x - r, y - r, x + r, y + r, fill="#0077dd", tags=("plot",))
                self._chart_point_ids.append(oid)
        # hide extra old ovals
        if len(self._chart_point_ids) > n:
            for oid in self._chart_point_ids[n:]:
                try:
                    self.chart_canvas.coords(oid, 0, 0, 0, 0)
                except Exception:
                    pass

    def _auto_refresh_chart(self):
        self._draw_chart()
        if self.root:
            self.root.after(self.ping_interval * 1000, self._auto_refresh_chart)

    # ---------------- Settings dialog / apply changes at runtime ----------------
    def _show_settings(self):
        dlg = tk.Toplevel(self.root)
        dlg.title("Settings")
        dlg.transient(self.root)
        dlg.grab_set()

        tk.Label(dlg, text="Ping interval (s):").grid(row=0, column=0, sticky="e", padx=5, pady=4)
        interval_var = tk.StringVar(value=str(self.ping_interval))
        tk.Entry(dlg, textvariable=interval_var).grid(row=0, column=1, padx=5, pady=4)

        tk.Label(dlg, text="Fail threshold:").grid(row=1, column=0, sticky="e", padx=5, pady=4)
        threshold_var = tk.StringVar(value=str(self.fail_threshold))
        tk.Entry(dlg, textvariable=threshold_var).grid(row=1, column=1, padx=5, pady=4)

        tk.Label(dlg, text="Max workers:").grid(row=2, column=0, sticky="e", padx=5, pady=4)
        workers_var = tk.StringVar(value=str(self.max_workers))
        tk.Entry(dlg, textvariable=workers_var).grid(row=2, column=1, padx=5, pady=4)

        tk.Label(dlg, text="Ping timeout (ms):").grid(row=3, column=0, sticky="e", padx=5, pady=4)
        timeout_var = tk.StringVar(value=str(self.ping_timeout_ms))
        tk.Entry(dlg, textvariable=timeout_var).grid(row=3, column=1, padx=5, pady=4)

        tk.Label(dlg, text="Log level:").grid(row=4, column=0, sticky="e", padx=5, pady=4)
        loglevel_var = tk.StringVar(value=logging.getLevelName(logger.level))
        loglevel_combo = ttk.Combobox(dlg, textvariable=loglevel_var, values=["DEBUG", "INFO", "WARNING", "ERROR"], state="readonly", width=10)
        loglevel_combo.grid(row=4, column=1, padx=5, pady=4)

        def on_ok():
            try:
                new_interval = max(1, int(interval_var.get()))
                new_threshold = max(1, int(threshold_var.get()))
                new_workers = max(1, int(workers_var.get()))
                new_timeout = max(200, int(timeout_var.get()))
                new_level_name = loglevel_var.get()
                new_level = getattr(logging, new_level_name, logging.INFO)
            except Exception:
                messagebox.showerror("Invalid", "Please enter valid integer values")
                return
            min_interval = max(1, math.ceil(new_timeout / 1000.0))
            if new_interval < min_interval:
                if not messagebox.askyesno("Interval vs Timeout", f"Ping timeout is {new_timeout}ms. Recommended interval >= {min_interval}s. Use {new_interval}s anyway?"):
                    return
            changed_workers = (new_workers != self.max_workers)
            self.ping_interval = new_interval
            self.fail_threshold = new_threshold
            self.max_workers = new_workers
            self.ping_timeout_ms = new_timeout
            self._set_log_level(new_level)
            self.write_log(f"[Settings] interval={self.ping_interval}s, timeout={self.ping_timeout_ms}ms, threshold={self.fail_threshold}, workers={self.max_workers}, log={new_level_name}")
            if changed_workers:
                self._create_executor()
            dlg.destroy()

        def on_cancel():
            dlg.destroy()

        tk.Button(dlg, text="OK", command=on_ok).grid(row=5, column=0, padx=5, pady=10)
        tk.Button(dlg, text="Cancel", command=on_cancel).grid(row=5, column=1, padx=5, pady=10)
        dlg.wait_window(dlg)

    def _set_log_level(self, level: int):
        logger.setLevel(level)
        for h in logger.handlers:
            try:
                h.setLevel(level)
            except Exception:
                pass

    # ---------------- Import / Export helpers ----------------
    def _import_hosts(self):
        path = filedialog.askopenfilename(title="Import hosts (JSON or plain list)", filetypes=[("JSON files", "*.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                raw = json.load(f)
            new_ips = []
            if isinstance(raw, dict) and "hosts" in raw:
                for h in raw["hosts"]:
                    ip = h.get("ip")
                    if ip:
                        new_ips.append(ip)
            elif isinstance(raw, dict) and "ips" in raw:
                new_ips = raw["ips"]
            elif isinstance(raw, list):
                new_ips = raw
            else:
                messagebox.showwarning("Import", "Unsupported JSON format")
                return
            added = 0
            with self.data_lock:
                for ip in new_ips:
                    if ip and ip not in self.ip_list and valid_host(ip):
                        self.ip_list.append(ip)
                        self.host_status[ip] = "Waiting"
                        self.fail_count[ip] = 0
                        self.delay_data[ip] = deque(maxlen=MAX_CHART_POINTS)
                        added += 1
            self.write_log(f"[Import] Added {added} hosts from {os.path.basename(path)}")
            self.save_hosts()
            self.refresh_host_tree()
        except Exception:
            logger.exception("Import hosts failed")
            messagebox.showerror("Import Error", "Failed to import hosts. See log for details.")

    def _export_hosts(self):
        path = filedialog.asksaveasfilename(title="Export hosts", defaultextension=".json", filetypes=[("JSON files", "*.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            with self.data_lock:
                export_ips = list(self.ip_list)
            with open(path, "w", encoding="utf-8") as f:
                json.dump({"ips": export_ips}, f, indent=2, ensure_ascii=False)
            self.write_log(f"[Export] Exported {len(export_ips)} hosts to {os.path.basename(path)}")
        except Exception:
            logger.exception("Export failed")
            messagebox.showerror("Export Error", "Failed to export hosts. See log for details.")

    # ---------------- About ----------------
    def _show_about(self):
        about_text = """PingOnly V1.1
Coded by Github Copilot, Desigined by Github/Code4AUTO
Updated on Jul 19 2026"""
        messagebox.showinfo("About", about_text)


# ===================== main =====================
def main():
    app = PingOnlyApp(
        ping_interval=DEFAULT_PING_INTERVAL,
        fail_threshold=DEFAULT_FAIL_THRESHOLD,
        max_workers=None,  # let app auto-select based on CPU/hosts
        ping_timeout_ms=DEFAULT_PING_TIMEOUT_MS,
    )
    app.run()


if __name__ == "__main__":
    main()