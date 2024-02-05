#!/usr/bin/env python
import os
import inspect
import linuxcnc
import hal, hal_glib
import time
import datetime
from datetime import date
import threading
import math
import inspect
import socket
from PyQt5 import QtCore, QtWidgets, QtGui
from PyQt5.QtCore import QThread, pyqtSignal, Qt, QMetaObject
try:
    from PyQt5.QtWebKitWidgets import QWebView
except ImportError:
    raise Exception("Qtvcp error with qtdragon - is package python-pyqt5.qtwebkit installed?")
from qtvcp.widgets.gcode_editor import GcodeEditor as GCODE
from qtvcp.widgets.mdi_line import MDILine as MDI_WIDGET
from qtvcp.widgets.tool_offsetview import ToolOffsetView as TOOL_TABLE
from qtvcp.widgets.origin_offsetview import OriginOffsetView as OFFSET_VIEW
from qtvcp.widgets.stylesheeteditor import  StyleSheetEditor as SSE
from qtvcp.widgets.file_manager import FileManager as FM
from qtvcp.lib.keybindings import Keylookup
from qtvcp.lib.gcodes import GCodes
from qtvcp.lib.toolbar_actions import ToolBarActions
from qtvcp.core import Status, Action, Info
from qtvcp import logger
from shutil import copyfile

LOG = logger.getLogger(__name__)
KEYBIND = Keylookup()
STATUS = Status()
INFO = Info()
ACTION = Action()
TOOLBAR = ToolBarActions()
STYLEEDITOR = SSE()

# constants for tab pages DEBE COINCIDIR CON EL NUMERO DE INDEX HTML
TAB_MAIN = 0
TAB_FILE = 1
TAB_CARGA = 3
TAB_DESCARGA = 2
TAB_STATUS = 6
TAB_GANTRY = 9
TAB_SETTINGS = 8
TAB_SEGREGADOR = 7
TAB_VOLTEADOR = 4
TAB_BLW_PARK = 5
TAB_TORNO = 10
TAB_NEUMATIC = 11
TAB_PATEADOR = 12



class HandlerClass:
    def __init__(self, halcomp, widgets, paths):
        self.h = halcomp
        self.w = widgets
        self.PATHS = paths
        self.gcodes = GCodes()
        self.valid = QtGui.QDoubleValidator(-999.999, 999.999, 3)
        
        KEYBIND.add_call('Key_F12','on_keycall_F12')
        KEYBIND.add_call('Key_Pause', 'on_keycall_pause')
                
        # some global variables
        self.run_time = 0
        self.hglib_pin = hal_glib.GPin
        self.hal = halcomp
        self.time_tenths = 0
        self.timerOn = False
        self.home_all = False
        self.system_list = ["G54","G55","G56","G57","G58","G59","G59.1","G59.2","G59.3"]
        self.slow_jog_factor = 10
        self.reload_tool = 0
        self.last_loaded_program = ""
        self.first_turnon = True
        self.inifile = linuxcnc.ini('../sim.qtvcp_screens.qtdragon/qtdragon.ini')
        self.program_not_od = '../sim.qtvcp_screens.qtdragon/ngc/program_not_od.ngc'
        self.program_od = '../sim.qtvcp_screens.qtdragon/ngc/program_od.ngc'
        self.program_empty = '../sim.qtvcp_screens.qtdragon/ngc/vacio.ngc'
        self.messages_log = '../sim.qtvcp_screens.qtdragon/logs/'
        self.thread = threading.Thread(target=self.master_init_conditions, args=(self.add_status,))
        self.threadUnload = threading.Thread(target=self.unload_routine)
        self.threadLoad = threading.Thread(target=self.load_routine)
        self.threadBlower = threading.Thread(target=self.blw_routine)
        self.threadTorno_entrar = threading.Thread(target=self.ch_routine_entrar)
        self.threadTorno_salir = threading.Thread(target=self.ch_routine_salir)
        self.threadPateador = threading.Thread(target=self.pateador_routine)
        self.lock = threading.Lock()
        self.TIMEOUT_PNEUMATIC = 8
        self.wait_time = 0.2
        self.flag_bd_pc = False
        self.err_routine = True
        self.chk_init_conditions = False
        self.safe_pos_x = 0
        self.safe_pos_y = 0
        self.safe_pos_z = 0
        self.safe_pos_offset = 0.3 
        self.ip_okuma = '192.168.1.2'
        self.lineedit_list = ["search_vel", "probe_vel", "max_probe", "eoffset_count"]
        self.onoff_list = ["frame_program", "frame_tool", "frame_dro", "frame_override", "frame_status"]
        self.couple_data_list = ["lineEdit_diametro_bruto", "lineEdit_diametro_torneado", "lineEdit_diametro_interno", "lineEdit_largo_bruto","lineEdit_largo_op10","lineEdit_largo_op20"]
        self.init_conditions_error_messages = {
            'carga': [],
            'descarga': [],
            'soplador': [],
            'torno_entrar': [],
            'torno_salir': [],
            'pateador': []
        }
        self.routine_error_messages = {
            'carga': [],
            'descarga': [],
            'soplador': [],
            'torno_entrar': [],
            'torno_salir': [],
            'pateador': []
        }
        self.auto_list = ["cmb_gcode_history"]
        self.html = """<html>
<head>
<title>Test page for the download:// scheme</title>
</head>
<body>
<h1>Setup Tab</h1>
<p>If you select a file with .html as a file ending, it will be shown here..</p>
<img src="file://%s" alt="lcnc_swoop" />
<hr />

<a href="http://www.linuxcnc.org/docs/2.8/html/gui/qtdragon.html">QtDragon Documentation link</a>
</body>
</html>
""" %(os.path.join(paths.IMAGEDIR,'lcnc_swoop.png'))

        STATUS.connect('general', self.dialog_return)
        STATUS.connect('state-on', lambda w: self.enable_onoff(True))
        STATUS.connect('state-off', lambda w: self.enable_onoff(False))
        STATUS.connect('mode-manual', lambda w: self.enable_auto(True))
        STATUS.connect('mode-mdi', lambda w: self.enable_auto(True))
        STATUS.connect('mode-auto', lambda w: self.enable_auto(False))
        STATUS.connect('gcode-line-selected', lambda w, line: self.set_start_line(line))
        STATUS.connect('hard-limits-tripped', self.hard_limit_tripped)
        STATUS.connect('interp-idle', lambda w: self.set_start_line(0))
       # STATUS.connect('program-pause-changed', lambda w, state: self.w.spindle_pause.setEnabled(state))
        STATUS.connect('user-system-changed', self.user_system_changed)
        STATUS.connect('file-loaded', self.file_loaded)
        STATUS.connect('homed', self.homed)
        STATUS.connect('all-homed', self.all_homed)
        STATUS.connect('not-all-homed', self.not_all_homed)
        STATUS.connect('periodic', lambda w: self.update_runtimer())
        STATUS.connect('command-running', lambda w: self.start_timer())
        STATUS.connect('command-stopped', lambda w: self.stop_timer())

    def class_patch__(self):
        self.old_fman = FM.load
        FM.load = self.load_code

    def initialized__(self):
        self.init_pins()
        self.init_preferences()
        self.init_widgets()
        self.iniciar_hilo()
        self.w.stackedWidget_log.setCurrentIndex(0)
        self.w.stackedWidget.setCurrentIndex(0)
        self.w.stackedWidget_dro.setCurrentIndex(0)
        #self.w.spindle_pause.setEnabled(False)
        self.w.btn_dimensions.setChecked(True)
        self.w.page_buttonGroup.buttonClicked.connect(self.main_tab_changed)
        self.w.filemanager.onUserClicked()    
        self.w.filemanager_usb.onMediaClicked()
        self.w.filemanager.list.setAlternatingRowColors(False)
        self.w.filemanager_usb.list.setAlternatingRowColors(False)
        STYLEEDITOR.loadStyleSheet('qtdragon_dark.qss')
        STYLEEDITOR.saveStyleSheet('qtdragon_dark.qss')
        STYLEEDITOR.on_applyButton_clicked()
        

        

    # hide widgets for A axis if not present
        #if "A" not in INFO.AVAILABLE_AXES:
        #    for i in self.axis_a_list:
        #        self.w[i].hide()
        #    self.w.lbl_increments_linear.setText("INCREMENTS")
    # set validators for lineEdit widgets
        # for val in self.lineedit_list:
        #     self.w['lineEdit_' + val].setValidator(self.valid)
        
    #############################
    # SPECIAL FUNCTIONS SECTION #
    #############################
    def init_pins(self):
        # safe pos ini
        self.safe_pos_x = self.inifile.find('INIT_SAFE_POSITIONS', 'X_POS') or 'unknow'
        self.safe_pos_y = self.inifile.find('INIT_SAFE_POSITIONS', 'Y_POS') or 'unknow'
        self.safe_pos_z = self.inifile.find('INIT_SAFE_POSITIONS', 'Z_POS') or 'unknow'

        pin = self.h.newpin("z-posRef", hal.HAL_FLOAT, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.gantry_z_safe_position)


        #print 'xpos: ', safe_pos_x, '\n', 'ypos: ', safe_pos_y, '\n', 'zpos: ', safe_pos_z 


        # spindle control pins
        pin = self.h.newpin("carga-errors", hal.HAL_FLOAT, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.carga_errors_changed)

        pin = self.h.newpin("spindle_volts", hal.HAL_FLOAT, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.spindle_pwr_changed)
        pin = self.h.newpin("spindle_fault", hal.HAL_U32, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.spindle_fault_changed)
        pin = self.h.newpin("modbus-errors", hal.HAL_U32, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.mb_errors_changed)

        pin = self.h.newpin("spindle_amps", hal.HAL_FLOAT, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.spindle_pwr_changed)


        # external offset control pins
        self.h.newpin("eoffset_enable", hal.HAL_BIT, hal.HAL_OUT)
        self.h.newpin("eoffset_clear", hal.HAL_BIT, hal.HAL_OUT)
        self.h.newpin("eoffset_count", hal.HAL_S32, hal.HAL_OUT)

        pin = self.h.newpin("x_EndingCodeFbk", hal.HAL_U32, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.x_end_code_changed)
        pin = self.h.newpin("x_StateFbk", hal.HAL_U32, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.x_state_changed)

        pin = self.h.newpin("y_EndingCodeFbk", hal.HAL_U32, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.y_end_code_changed)
        pin = self.h.newpin("y_StateFbk", hal.HAL_U32, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.y_state_changed)

        pin = self.h.newpin("z_EndingCodeFbk", hal.HAL_U32, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.z_end_code_changed)
        pin = self.h.newpin("z_StateFbk", hal.HAL_U32, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.z_state_changed)

        # pin = self.h.newpin("z_StateFbk", hal.HAL_U32, hal.HAL_IN)
        # hal_glib.GPin(pin).connect("value_changed", self.z_state_changed)
        # pin = self.h.newpin("z_StateFbk", hal.HAL_U32, hal.HAL_IN)
        # hal_glib.GPin(pin).connect("value_changed", self.z_state_changed)
        # pin = self.h.newpin("z_StateFbk", hal.HAL_U32, hal.HAL_IN)
        # hal_glib.GPin(pin).connect("value_changed", self.z_state_changed)

        pin = self.h.newpin("eoffset_value", hal.HAL_FLOAT, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.eoffset_changed)
        
        self.py_in_nc_pins = {'SEN_bd_full': 0}
        self.py_in_pins = {#'SEN_gr_d_open': 0,
							#'SEN_gr_d_closed': 0,
							#'SEN_gr_d_pc': 0,
							#'SEN_gr_u_closed': 0,
							#'SEN_gr_u_open': 0,
							#'SEN_gr_u_pc': 0,
							#'SEN_tor_gate_open': 0,
							#'SEN_tor_gate_closed': 0,
							#'RI_tor_ep_confirm': 0,
							#'RI_tor_home_confirm': 0,
							#'RI_tor_alarm_confirm': 0,
							#'RI_tor_ofm': 0, #estado de salida gantry
							#'RI_tor_cs':0, #estado de salida gantry
							#'SEN_park_pc': 0,
							#'SEN_blw_closed': 0,
							#'SEN_blw_open': 0,
							#'SEN_blw_pc': 0,
							#'SEN_volt_claw_open': 0,
							#'SEN_volt_claw_closed': 0,
							#'SEN_volt_0_side': 0,
							#'SEN_volt_180_side': 0,
							#'SEN_seg_pc': 0,
							#'SEN_seg_overturn': 0,
							#'SEN_seg_idle': 0,
							#'SEN_bc_down': 0,
							#'SEN_bc_up': 0,
							#'SEN_bc_pc': 0,
							#'SEN_bd_pc': 0,
							#'SEN_bd_up': 0,
							#'SEN_bd_down': 0,
							'SEN_bd_full': 0,
							}       
        self.py_out_pins = {'EV_gr_d_open':0,
							'EV_gr_d_closed':0,
							'EV_gr_u_open':0,
							'EV_gr_u_closed':0,
							'EV_tor_gate_open':0,
							'EV_tor_gate_closed':0,
							'EV_blw_close_cobertor':0,
							'EV_blw_open_cobertor':0,
							'EV_blw_on':0,
							'EV_blw_off':0,
							'EV_volt_claw_open':0,
							'EV_volt_claw_closed':0,
							'EV_volt_0_side':0,
							'EV_volt_180_side':0,
							'EV_seg_overturn':0,
							'EV_seg_idle':0,
							'EV_bc_down':0,
							'EV_bc_up':0,
                            'EV_bc_frw':0,
                            'EV_bc_bkw':0,
							'EV_bd_up':0,
							'EV_bd_down':0,
                            'EV_bd_frw':0,
                            'EV_bd_bkw':0,
                            'EV_pat_frw':0,
                            'EV_pat_bkw':0,
                            'EV_pat_down':0,
                            'EV_pat_up':0,
                            'resetFaults':0,
                            'RI_tor_cc':0,
                            'RI_tor_cu':0,
                            'RI_tor_so1':0,
                            'RI_tor_so2':0,
                            'RI_tor_ofm':0,
                            'RI_tor_cs':0,
                            'RI_tor_spare':0,
                            'RI_tor_mfin':0,
                            'RI_tor_sl':0,
                            'RI_tor_ga':0,
							}
        self.py_control_pins = {'CTRL_bc_ogr':0,
								'CTRL_bd_ogr':0,
								'CTRL_blw_ogr':0,
								'CTRL_blw_sr':0,#start routine
								'CTRL_blw_er':0,#end routine
								'CTRL_ch_ce':0, #okuma can enter(gantry)
                                'CTRL_ch_od':0, #led od version
                                'CTRL_init_master':0, #led master init (err_routine)
                                'CTRL_end_cycle':0
							}



        #declaracion de pines de control en python
        for name,value in self.py_control_pins.items():
            self.pin_control = self.hglib_pin(self.h.newpin(name, hal.HAL_BIT, hal.HAL_IN))
            if str(name) in self.py_control_pins:
                self.py_control_pins.update({str(name): self.pin_control})

        #declaracion de pines de entrada en python
        pin = self.h.newpin("SEN_bd_full", hal.HAL_BIT, hal.HAL_IN)
        hal_glib.GPin(pin).connect("value_changed", self.change_value)
        #for name,value in self.py_in_pins.items():
        #    self.pin_in = self.hglib_pin(self.h.newpin(name, hal.HAL_BIT, hal.HAL_IN))
        #    if str(name) in self.py_in_pins:
        #        self.py_in_pins.update({str(name): self.pin_in})
        #        if str(name) in self.py_in_nc_pins:
        #            self.pin_in.connect("value_changed", self.change_value)
                
        #declaracion de pines de salida en python
        for name,value in self.py_out_pins.items():
            self.pin_out = self.hglib_pin(self.h.newpin(name, hal.HAL_BIT, hal.HAL_IN))
            if str(name) in self.py_out_pins:
                self.py_out_pins.update({str(name): self.pin_out})


        for n in self.py_out_pins:
            if n.split("_")[0] == "RI":
                if self.py_out_pins[n].get() == False:
                    self.w[n].setStyleSheet("color:red")
                else:
                    self.w[n].setStyleSheet("color:green")
        #print('el pin es',(hal.get_value('SEN_bd_down')))
        # print('los widgets son',self.w.sender().property('sensor'))



    def change_value(self,pin):
        #print('cambia valor de sensor')
        if self.threadUnload.is_alive() == True:
            self.flag_bd_pc = False
        #return

         
    def init_preferences(self):
        if not self.w.PREFS_:
            self.add_status("CRITICAL - no preference file found, enable preferences in screenoptions widget")
            return
        self.last_loaded_program = self.w.PREFS_.getpref('last_loaded_file', None, str,'BOOK_KEEPING')
        self.reload_tool = self.w.PREFS_.getpref('Tool to load', 0, int,'CUSTOM_FORM_ENTRIES')
        #self.w.lineEdit_laser_x.setText(str(self.w.PREFS_.getpref('Laser X', 100, float, 'CUSTOM_FORM_ENTRIES')))
        #self.w.lineEdit_laser_y.setText(str(self.w.PREFS_.getpref('Laser Y', -20, float, 'CUSTOM_FORM_ENTRIES')))
        #self.w.lineEdit_sensor_x.setText(str(self.w.PREFS_.getpref('Sensor X', 10, float, 'CUSTOM_FORM_ENTRIES')))
        #self.w.lineEdit_sensor_y.setText(str(self.w.PREFS_.getpref('Sensor Y', 10, float, 'CUSTOM_FORM_ENTRIES')))
        #self.w.lineEdit_work_height.setText(str(self.w.PREFS_.getpref('Work Height', 20, float, 'CUSTOM_FORM_ENTRIES')))
        #self.w.lineEdit_touch_height.setText(str(self.w.PREFS_.getpref('Touch Height', 40, float, 'CUSTOM_FORM_ENTRIES')))
        #self.w.lineEdit_sensor_height.setText(str(self.w.PREFS_.getpref('Sensor Height', 40, float, 'CUSTOM_FORM_ENTRIES')))
        # self.w.lineEdit_search_vel.setText(str(self.w.PREFS_.getpref('Search Velocity', 40, float, 'CUSTOM_FORM_ENTRIES')))
        # self.w.lineEdit_probe_vel.setText(str(self.w.PREFS_.getpref('Probe Velocity', 10, float, 'CUSTOM_FORM_ENTRIES')))
        # self.w.lineEdit_max_probe.setText(str(self.w.PREFS_.getpref('Max Probe', 10, float, 'CUSTOM_FORM_ENTRIES')))
        #self.w.lineEdit_eoffset_count.setText(str(self.w.PREFS_.getpref('Eoffset count', 0, int, 'CUSTOM_FORM_ENTRIES')))
        #self.w.chk_eoffsets.setChecked(self.w.PREFS_.getpref('External offsets', False, bool, 'CUSTOM_FORM_ENTRIES'))
        #self.w.chk_reload_program.setChecked(self.w.PREFS_.getpref('Reload program', False, bool,'CUSTOM_FORM_ENTRIES'))
        # self.w.chk_reload_tool.setChecked(self.w.PREFS_.getpref('Reload tool', False, bool,'CUSTOM_FORM_ENTRIES'))
        self.w.chk_use_keyboard.setChecked(self.w.PREFS_.getpref('Use keyboard', False, bool, 'CUSTOM_FORM_ENTRIES'))
        #self.w.chk_run_from_line.setChecked(self.w.PREFS_.getpref('Run from line', False, bool, 'CUSTOM_FORM_ENTRIES'))
        #self.w.chk_use_virtual.setChecked(self.w.PREFS_.getpref('Use virtual keyboard', False, bool, 'CUSTOM_FORM_ENTRIES'))
        #self.w.chk_alpha_mode.setChecked(self.w.PREFS_.getpref('Use alpha display mode', False, bool, 'CUSTOM_FORM_ENTRIES'))
        self.w.chk_inhibit_selection.setChecked(self.w.PREFS_.getpref('Inhibit display mouse selection', True, bool, 'CUSTOM_FORM_ENTRIES'))

    def closing_cleanup__(self):
        if not self.w.PREFS_: return
        self.w.PREFS_.putpref('last_loaded_directory', os.path.dirname(self.last_loaded_program), str, 'BOOK_KEEPING')
        self.w.PREFS_.putpref('last_loaded_file', self.last_loaded_program, str, 'BOOK_KEEPING')
        self.w.PREFS_.putpref('Tool to load', STATUS.get_current_tool(), int, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('Laser X', self.w.lineEdit_laser_x.text().encode('utf-8'), float, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('Laser Y', self.w.lineEdit_laser_y.text().encode('utf-8'), float, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('Sensor X', self.w.lineEdit_sensor_x.text().encode('utf-8'), float, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('Sensor Y', self.w.lineEdit_sensor_y.text().encode('utf-8'), float, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('Work Height', self.w.lineEdit_work_height.text().encode('utf-8'), float, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('Touch Height', self.w.lineEdit_touch_height.text().encode('utf-8'), float, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('Sensor Height', self.w.lineEdit_sensor_height.text().encode('utf-8'), float, 'CUSTOM_FORM_ENTRIES')
        # self.w.PREFS_.putpref('Search Velocity', self.w.lineEdit_search_vel.text().encode('utf-8'), float, 'CUSTOM_FORM_ENTRIES')
        # self.w.PREFS_.putpref('Probe Velocity', self.w.lineEdit_probe_vel.text().encode('utf-8'), float, 'CUSTOM_FORM_ENTRIES')
        # self.w.PREFS_.putpref('Max Probe', self.w.lineEdit_max_probe.text().encode('utf-8'), float, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('Eoffset count', self.w.lineEdit_eoffset_count.text().encode('utf-8'), int, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('External offsets', self.w.chk_eoffsets.isChecked(), bool, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('Reload program', self.w.chk_reload_program.isChecked(), bool, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('Reload tool', self.w.chk_reload_tool.isChecked(), bool, 'CUSTOM_FORM_ENTRIES')
        self.w.PREFS_.putpref('Use keyboard', self.w.chk_use_keyboard.isChecked(), bool, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('Run from line', self.w.chk_run_from_line.isChecked(), bool, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('Use virtual keyboard', self.w.chk_use_virtual.isChecked(), bool, 'CUSTOM_FORM_ENTRIES')
        #self.w.PREFS_.putpref('Use alpha display mode', self.w.chk_alpha_mode.isChecked(), bool, 'CUSTOM_FORM_ENTRIES')
        self.w.PREFS_.putpref('Inhibit display mouse selection', self.w.chk_inhibit_selection.isChecked(), bool, 'CUSTOM_FORM_ENTRIES')

    def init_widgets(self):
        #print('ruta de los mensajes: ',self.messages_log)
        self.w.main_tab_widget.setCurrentIndex(0)
        self.w.slider_jog_linear.setValue(INFO.DEFAULT_LINEAR_JOG_VEL)
        #self.w.slider_jog_angular.setMaximum(INFO.MAX_ANGULAR_JOG_VEL)
        #self.w.slider_jog_angular.setValue(INFO.DEFAULT_ANGULAR_JOG_VEL)
        self.w.slider_feed_ovr.setMaximum(INFO.MAX_FEED_OVERRIDE)
        self.w.slider_feed_ovr.setValue(100)
        self.w.slider_rapid_ovr.setMaximum(100)
        self.w.slider_rapid_ovr.setValue(100)
        #self.w.slider_spindle_ovr.setMinimum(INFO.MIN_SPINDLE_OVERRIDE)
        #self.w.slider_spindle_ovr.setMaximum(INFO.MAX_SPINDLE_OVERRIDE)
        #self.w.slider_spindle_ovr.setValue(100)
        self.w.chk_override_limits.setChecked(False)
        self.w.chk_override_limits.setEnabled(True)
        self.w.lbl_maxv_percent.setText("100 %")
        self.w.lbl_max_rapid.setText(str(INFO.MAX_TRAJ_VELOCITY))
        # self.w.lbl_home_x.setText(INFO.get_error_safe_setting('JOINT_0', 'HOME',"50"))
        # self.w.lbl_home_y.setText(INFO.get_error_safe_setting('JOINT_1', 'HOME',"50"))
        self.w.cmb_gcode_history.addItem("No File Loaded")
        self.w.cmb_gcode_history.wheelEvent = lambda event: None
        self.w.jogincrements_linear.wheelEvent = lambda event: None
        #self.w.jogincrements_angular.wheelEvent = lambda event: None
        self.w.gcode_editor.hide()

        #set up gcode list
        self.gcodes.setup_list()
        # clickable frames
        self.w.frame_cycle_start.mousePressEvent = self.btn_start_clicked
        self.w.frame_home_all.mousePressEvent = self.btn_home_all_clicked
        # web view widget for SETUP page
        self.web_view = QWebView()
        self.w.verticalLayout_setup.addWidget(self.web_view)
        self.web_view.setHtml(self.html)
        # check for virtual keyboard enabled
        # if self.w.chk_use_virtual.isChecked():
        #     self.w.btn_keyboard.show()
        # else:
        #     self.w.btn_keyboard.hide()
        TOOLBAR.configure_statusbar(self.w.statusbar,'message_recall')

        if not INFO.MACHINE_IS_METRIC:
            self.w.lbl_jog_linear.setText('JOG RATE\nINCH/MIN')
            self.w.lbl_tool_sensor_B2W.setText('INCH')
            self.w.lbl_tool_sensor_B2S.setText('INCH')
            self.w.lbl_touchheight_units.setText('INCH')

    def processed_focus_event__(self, receiver, event):
        #if not self.w.chk_use_virtual.isChecked() or STATUS.is_auto_mode(): return
        # if isinstance(receiver, QtWidgets.QLineEdit):
        #     if not receiver.isReadOnly():
        #         self.w.stackedWidget_dro.setCurrentIndex(1)
        # elif isinstance(receiver, QtWidgets.QTableView):
        #     self.w.stackedWidget_dro.setCurrentIndex(1)
        # elif isinstance(receiver, QtWidgets.QCommonStyle):
            return
    
    def processed_key_event__(self,receiver,event,is_pressed,key,code,shift,cntrl):
        # when typing in MDI, we don't want keybinding to call functions
        # so we catch and process the events directly.
        # We do want ESC, F1 and F2 to call keybinding functions though
        if code not in(QtCore.Qt.Key_Escape,QtCore.Qt.Key_F1 ,QtCore.Qt.Key_F2,
                    QtCore.Qt.Key_F12):

            # search for the top widget of whatever widget received the event
            # then check if it's one we want the keypress events to go to
            flag = False
            receiver2 = receiver
            while receiver2 is not None and not flag:
                if isinstance(receiver2, QtWidgets.QDialog):
                    flag = True
                    break
                if isinstance(receiver2, QtWidgets.QLineEdit):
                    flag = True
                    break
                if isinstance(receiver2, MDI_WIDGET):
                    flag = True
                    break
                if isinstance(receiver2, GCODE):
                    flag = True
                    break
                if isinstance(receiver2, TOOL_TABLE):
                    flag = True
                    break
                if isinstance(receiver2, OFFSET_VIEW):
                    flag = True
                    break
                receiver2 = receiver2.parent()

            if flag:
                if isinstance(receiver2, GCODE):
                    # if in manual or in readonly mode do our keybindings - otherwise
                    # send events to gcode widget
                    if STATUS.is_man_mode() == False or not receiver2.isReadOnly():
                        if is_pressed:
                            receiver.keyPressEvent(event)
                            event.accept()
                        return True
                elif is_pressed:
                    receiver.keyPressEvent(event)
                    event.accept()
                    return True
                else:
                    event.accept()
                    return True

        if event.isAutoRepeat():return True

        # ok if we got here then try keybindings function calls
        # KEYBINDING will call functions from handler file as
        # registered by KEYBIND.add_call(KEY,FUNCTION) above
        return KEYBIND.manage_function_calls(self,event,is_pressed,key,shift,cntrl)

    #########################
    # CALLBACKS FROM STATUS #
    #########################

    def spindle_pwr_changed(self, data):
        # this calculation assumes the voltage is line to neutral
        # and that the synchronous motor spindle has a power factor of 0.9
        power = self.h['spindle_volts'] * self.h['spindle_amps'] * 2.7 # 3 x V x I x PF
        amps = "{:1.1f}".format(self.h['spindle_amps'])
        pwr = "{:1.1f}".format(power)
        #self.w.lbl_spindle_amps.setText(amps)
        #self.w.lbl_spindle_power.setText(pwr)

    def spindle_fault_changed(self, data):
        fault = hex(self.h['spindle_fault'])
        #self.w.lbl_spindle_fault.setText(fault)

    def mb_errors_changed(self, data):
        return
        # errors = self.h['modbus-errors']
        # self.w.lbl_mb_errors.setText(str(errors))

    def carga_errors_changed(self, data):
        #master
        flag_print_value = int(data.value)
        if flag_print_value == 1:
            for key, lista in self.routine_error_messages.items():
                if len(lista) > 0:
                    for value in lista:
                        self.add_status(value)
                    self.routine_error_messages[key] = []
        self.h['carga-errors'] = 0
        return


    def x_end_code_changed(self, data):
        state = self.h['x_EndingCodeFbk']
        self.w.lbl_x_EndingCodeFbk.setText(str(state))

    def gantry_z_safe_position(self, data):
        #print("valor de z actualizado",data.get())
        pos = data.get()
        if pos >= (int(self.safe_pos_z) - self.safe_pos_offset) and pos <= (int(self.safe_pos_z) + self.safe_pos_offset):
            self.py_out_pins['RI_tor_ofm'].set(True)
        else:
            self.py_out_pins['RI_tor_ofm'].set(False)

    def x_state_changed(self, data):
        state = self.h['x_StateFbk']
        self.w.lbl_x_StateFbk.setText(str(state))

    def y_end_code_changed(self, data):
        state = self.h['y_EndingCodeFbk']
        self.w.lbl_y_EndingCodeFbk.setText(str(state))

    def y_state_changed(self, data):
        state = self.h['y_StateFbk']
        self.w.lbl_y_StateFbk.setText(str(state))

    def z_end_code_changed(self, data):
        state = self.h['z_EndingCodeFbk']
        self.w.lbl_z_EndingCodeFbk.setText(str(state))

    def z_state_changed(self, data):
        state = self.h['z_StateFbk']
        self.w.lbl_z_StateFbk.setText(str(state))
    
    # def hours_state_changed(self, data):
    #     state = hal.get_value('time.0.hours')
    #     self.w.lbl_hours_StartRoutine.setText(str(state))
        
    # def minutes_state_changed(self, data):
    #     state = hal.get_value('time.0.minutes')
    #     self.w.lbl_minutes_StartRoutine.setText(str(state))

    # def seconds_state_changed(self, data):
    #     state = hal.get_value('time.0.seconds')
    #     self.w.lbl_seconds_StartRoutine.setText(str(state))


    

    def eoffset_changed(self, data):
        eoffset = "{:2.3f}".format(self.h['eoffset_value'])
        #self.w.lbl_eoffset_value.setText(eoffset)

    def dialog_return(self, w, message):
        rtn = message.get('RETURN')
        name = message.get('NAME')
        plate_code = bool(message.get('ID') == '_touchplate_')
        sensor_code = bool(message.get('ID') == '_toolsensor_')
        wait_code = bool(message.get('ID') == '_wait_resume_')
        if plate_code and name == 'MESSAGE' and rtn is True:
            self.touchoff('touchplate')
        elif sensor_code and name == 'MESSAGE' and rtn is True:
            self.touchoff('sensor')
        elif wait_code and name == 'MESSAGE':
            self.h['eoffset_clear'] = False

    def user_system_changed(self, obj, data):
        sys = self.system_list[int(data) - 1]
        #self.w.offset_table.selectRow(int(data) + 3)
        self.w.actionbutton_rel.setText(sys)

    def file_loaded(self, obj, filename):
        if filename is not None:
            self.add_status("Loaded file {}".format(filename))
            self.w.progressBar.setValue(0)
            self.last_loaded_program = filename
            self.w.lbl_runtime.setText("00:00:00")
        else:
            self.add_status("Filename not valid")

    def percent_loaded_changed(self, fraction):
        if fraction <0:
            self.w.progressBar.setValue(0)
            self.w.progressBar.setFormat('Progress')
        else:
            self.w.progressBar.setValue(fraction)
            self.w.progressBar.setFormat('Loading: {}%'.format(fraction))

    def percent_completed_changed(self, fraction):
        self.w.progressBar.setValue(fraction)
        if fraction <0:
            self.w.progressBar.setValue(0)
            self.w.progressBar.setFormat('Progress')
        else:
            self.w.progressBar.setFormat('Completed: {}%'.format(fraction))

    def homed(self, obj, joint):
        i = int(joint)
        axis = INFO.GET_NAME_FROM_JOINT.get(i).lower()
        try:
            self.w["dro_axis_{}".format(axis)].setProperty('homed', True)
            self.w["dro_axis_{}".format(axis)].setStyle(self.w["dro_axis_{}".format(axis)].style())
        except:
            pass

    def all_homed(self, obj):
        self.home_all = True
        self.w.lbl_home_all.setText("ALL\nHOMED")
        if self.first_turnon is True:
            self.first_turnon = False
            # if self.w.chk_reload_tool.isChecked():
            #     command = "M61 Q{}".format(self.reload_tool)
            #     ACTION.CALL_MDI(command)
            # if self.last_loaded_program is not None and self.w.chk_reload_program.isChecked():
            #     if os.path.isfile(self.last_loaded_program):
            #         self.w.cmb_gcode_history.addItem(self.last_loaded_program)
            #         self.w.cmb_gcode_history.setCurrentIndex(self.w.cmb_gcode_history.count() - 1)
            #         ACTION.OPEN_PROGRAM(self.last_loaded_program)
            #         self.w.manual_mode_button.setChecked(True)

    def not_all_homed(self, obj, list):
        self.home_all = False
        self.w.lbl_home_all.setText("HOME\nALL")
        for i in INFO.AVAILABLE_JOINTS:
            if str(i) in list:
                axis = INFO.GET_NAME_FROM_JOINT.get(i).lower()
                try:
                    self.w["dro_axis_{}".format(axis)].setProperty('homed', False)
                    self.w["dro_axis_{}".format(axis)].setStyle(self.w["dro_axis_{}".format(axis)].style())
                except:
                    pass

    def hard_limit_tripped(self, obj, tripped, list_of_tripped):
        return
        #self.add_status("Hard limits tripped")
        #self.w.chk_override_limits.setEnabled(tripped)
        # if not tripped:
        #     self.w.chk_override_limits.setChecked(False)

    def update_runtimer(self):
        if self.timerOn is False or STATUS.is_auto_paused(): return
        self.time_tenths += 1
        if self.time_tenths == 10:
            self.time_tenths = 0
            self.run_time += 1
            hours, remainder = divmod(self.run_time, 3600)
            minutes, seconds = divmod(remainder, 60)
            self.w.lbl_runtime.setText("{:02d}:{:02d}:{:02d}".format(hours, minutes, seconds))

    def start_timer(self):
        if STATUS.is_auto_running():
            self.run_time = 0
            self.timerOn = True

    def stop_timer(self):
        self.timerOn = False

    #######################
    # CALLBACKS FROM FORM #
    #######################

    # main button bar
    def main_tab_changed(self, btn):
        index = btn.property("index")
        index_neumatic = btn.property("index_neumatic")
        index_axis = btn.property("index_axis")

        # print ('index number',index)
        # print ('index_neumatic',index_neumatic)
        # print ('index_axis',index_axis)

        if index is None: return
        # if in automode still allow settings to show so override limits can be used
        if STATUS.is_auto_mode() and index !=8:
            self.add_status("Cannot switch pages while in AUTO mode")
            # make sure main page is showing
            self.w.main_tab_widget.setCurrentIndex(0)
            self.w.btn_main.setChecked(True)
            return
        #esto es lo que carga el main widget, el numero corresponde a la posisicon en la que sta en el codigo que se trae del numero index del html
        if index != TAB_CARGA and index != TAB_DESCARGA and index != TAB_SEGREGADOR and index != TAB_VOLTEADOR and index != TAB_BLW_PARK and index != TAB_TORNO and index != TAB_GANTRY and index != TAB_PATEADOR and index_axis == None:
            self.w.main_tab_widget.setCurrentIndex(index)
            self.w.stackedWidget_neumatic.setCurrentIndex(0)
        else:
            if index_axis != None:
                self.w.stackedWidget_axis.setCurrentIndex(index_axis)
            else:
                self.w.stackedWidget_neumatic.setCurrentIndex(index_neumatic)
        #self.w.main_tab_widget.setCurrentIndex(14)

        #self.w.stackedWidget_neumatic.setCurrentIndex(1)
        #print(self.w.stackedWidget_neumatic)
        #esto es para los chiquitos de la izqurda, el numero corresponde a la posisicon en la que sta en el codigo
        if index == TAB_MAIN:
            self.w.stackedWidget.setCurrentIndex(0)
        elif index == TAB_FILE:
            self.w.stackedWidget.setCurrentIndex(1)
        elif index == TAB_CARGA:
            self.w.stackedWidget.setCurrentIndex(2)
        elif index == TAB_DESCARGA:
            self.w.stackedWidget.setCurrentIndex(3)
        elif index == TAB_SEGREGADOR:
            self.w.stackedWidget.setCurrentIndex(4)
        elif index == TAB_VOLTEADOR:
            self.w.stackedWidget.setCurrentIndex(5)
        elif index == TAB_BLW_PARK:
            self.w.stackedWidget.setCurrentIndex(6)
        elif index == TAB_GANTRY:
            self.w.stackedWidget.setCurrentIndex(7)
        elif index == TAB_TORNO:
            self.w.stackedWidget.setCurrentIndex(8)
        elif index == TAB_PATEADOR:
            self.w.stackedWidget.setCurrentIndex(9)
        else:
            self.w.stackedWidget.setCurrentIndex(0)
        
        #print(help(self.w.stackedWidget.setCurrentIndex))
        #for item in dir(self.w.stackedWidget):
        #    print(item)

    # gcode frame
    def cmb_gcode_history_clicked(self):
        if self.w.cmb_gcode_history.currentIndex() == 0: return
        filename = self.w.cmb_gcode_history.currentText().encode('utf-8')
        if filename == self.last_loaded_program:
            self.add_status("Selected program is already loaded")
        else:
            ACTION.OPEN_PROGRAM(filename)

    # program frame
    def btn_start_clicked(self, obj):
        if self.w.main_tab_widget.currentIndex() != 0:
            return
        if not STATUS.is_auto_mode():
            self.add_status("Must be in AUTO mode to run a program")
            return
        start_line = int(self.w.lbl_start_line.text().encode('utf-8'))
        self.add_status("Started program from line {}".format(start_line))
        self.run_time = 0
        if start_line == 1:
            ACTION.RUN(start_line)
        else:
            # instantiate preset dialog
            info = '<b>Running from Line: {} <\b>'.format(start_line)
            mess = {'NAME':'RUNFROMLINE', 'TITLE':'Preset Dialog', 'ID':'_RUNFROMLINE', 'MESSAGE':info, 'LINE':start_line}
            ACTION.CALL_DIALOG(mess)

    def btn_reload_file_clicked(self):
        if self.last_loaded_program:
            self.w.progressBar.setValue(0)
            self.add_status("Loaded program file {}".format(self.last_loaded_program))
            ACTION.OPEN_PROGRAM(self.last_loaded_program)

    # DRO frame
    def btn_home_all_clicked(self, obj):
        if self.home_all is False:
            ACTION.SET_MACHINE_HOMING(-1)
        else:
            ACTION.SET_MACHINE_UNHOMED(-1)

    def btn_home_clicked(self):
        joint = self.w.sender().property('joint')
        axis = INFO.GET_NAME_FROM_JOINT.get(joint).lower()
        if self.w["dro_axis_{}".format(axis)].property('homed') is True:
            ACTION.SET_MACHINE_UNHOMED(joint)
        else:
            ACTION.SET_MACHINE_HOMING(joint)

    # tool frame
    def disable_pause_buttons(self, state):
        return
        # self.w.action_pause.setEnabled(not state)
        # self.w.action_step.setEnabled(not state)
        # if state:
        # # set external offsets to lift spindle
        #     self.h['eoffset_enable'] = self.w.chk_eoffsets.isChecked()
        #     fval = float(self.w.lineEdit_eoffset_count.text())
        #     self.h['eoffset_count'] = int(fval)
        # else:
        #     self.h['eoffset_count'] = 0
        #     self.h['eoffset_clear'] = True
        # # instantiate warning box
        #     info = "Wait for spindle at speed signal before resuming"
        #     mess = {'NAME':'MESSAGE', 'ICON':'WARNING', 'ID':'_wait_resume_', 'MESSAGE':'CAUTION', 'MORE':info, 'TYPE':'OK'}
        #     ACTION.CALL_DIALOG(mess)


    def test_button(self):
        #while True:
        #    key = (self.w.sender().objectName())
        #    self.py_out_pins[key].set(True)
        #self.py_out_pins[key].set(False)

        #self.py_out_pins['btn_subir_d'].set(True)
        print('test_buttontest_buttontest_buttontest_buttontest_buttontest_button')
        #send neumatic commands

    def btn_od_version(self):
        key = (self.w.sender().objectName())
        if self.py_control_pins[key].get() == False:
            STYLEEDITOR.loadStyleSheet('qtdragon_od.qss')
            STYLEEDITOR.saveStyleSheet('qtdragon_od.qss')
            STYLEEDITOR.on_applyButton_clicked()
            self.py_control_pins[key].set(True)
            
        else:
            STYLEEDITOR.loadStyleSheet('qtdragon_dark.qss')
            STYLEEDITOR.saveStyleSheet('qtdragon_dark.qss')
            STYLEEDITOR.on_applyButton_clicked()
            self.py_control_pins[key].set(False)


    def btn_pressed_cmd(self):
        key = (self.w.sender().objectName())
        self.py_out_pins[key].set(True)

    def btn_released_cmd(self):
        key = (self.w.sender().objectName())
        self.py_out_pins[key].set(False)

        
    def btn_receiver_neumatic_cmd(self):#, key
        key = (self.w.sender().objectName())
        try:
            self.py_out_pins[key].set(True)
            time.sleep(0.2)
            self.py_out_pins[key].set(False)
            #return True
        except:
            return False

        
    # override frame
    def slow_button_clicked(self, state):
        slider = self.w.sender().property('slider')
        current = self.w[slider].value()
        max = self.w[slider].maximum()
        if state:
            self.w.sender().setText("SLOW")
            self.w[slider].setMaximum(max / self.slow_jog_factor)
            self.w[slider].setValue(current / self.slow_jog_factor)
            self.w[slider].setPageStep(10)
        else:
            self.w.sender().setText("FAST")
            self.w[slider].setMaximum(max * self.slow_jog_factor)
            self.w[slider].setValue(current * self.slow_jog_factor)
            self.w[slider].setPageStep(100)

    def slider_maxv_changed(self, value):
        maxpc = (float(value) / INFO.MAX_TRAJ_VELOCITY) * 100
        self.w.lbl_maxv_percent.setText("{:5.2f} %".format(maxpc))

    def slider_rapid_changed(self, value):
        rapid = (float(value) / 100) * INFO.MAX_TRAJ_VELOCITY
        self.w.lbl_max_rapid.setText("{:5.1f}".format(rapid))

    def btn_maxv_100_clicked(self):
        self.w.slider_maxv_ovr.setValue(INFO.MAX_TRAJ_VELOCITY)

    def btn_maxv_50_clicked(self):
        self.w.slider_maxv_ovr.setValue(INFO.MAX_TRAJ_VELOCITY / 2)

    # file tab
    def btn_gcode_edit_clicked(self, state):
        if not STATUS.is_on_and_idle():
            return
        if state:
            self.w.filemanager.hide()
            self.w.widget_file_copy.hide()
            self.w.gcode_editor.show()
            self.w.gcode_editor.editMode()
        else:
            self.w.filemanager.show()
            self.w.widget_file_copy.show()
            self.w.gcode_editor.hide()
            self.w.gcode_editor.readOnlyMode()

    def btn_load_file_clicked(self):
        fname = self.w.filemanager.getCurrentSelected()
        if fname[1] is True:
            self.load_code(fname[0])
        print("el archivo es:",fname[0])

    #boton editar
    def btn_edit_couple_data_clicked(self):
        for widget in self.couple_data_list:
            self.w[widget].setEnabled(True)
        #fname = dir(self.w.filemanager)
        #print(fname)
        self.load_code("")
        #print(dir(self.w.isEnabled()))
        #fname = self.w.filemanager.getCurrentSelected()
        #if fname[1] is True:
        #    self.load_code(fname[0])

    def btn_copy_file_clicked(self):
        if self.w.sender() == self.w.btn_copy_right:
            source = self.w.filemanager_usb.getCurrentSelected()
            target = self.w.filemanager.getCurrentSelected()
        elif self.w.sender() == self.w.btn_copy_left:
            source = self.w.filemanager.getCurrentSelected()
            target = self.w.filemanager_usb.getCurrentSelected()
        else:
            return
        if source[1] is False:
            self.add_status("Specified source is not a file")
            return
        if target[1] is True:
            destination = os.path.join(os.path.dirname(target[0]), os.path.basename(source[0]))
        else:
            destination = os.path.join(target[0], os.path.basename(source[0]))
        try:
            copyfile(source[0], destination)
            self.add_status("Copied file from {} to {}".format(source[0], destination))
        except Exception as e:
            self.add_status("Unable to copy file. %s" %e)

    # offsets tab
    def btn_goto_sensor_clicked(self):
        #x = float(self.w.lineEdit_sensor_x.text())
        #y = float(self.w.lineEdit_sensor_y.text())
        if not STATUS.is_metric_mode():
            x = x / 25.4
            y = y / 25.4
        ACTION.CALL_MDI("G90")
        ACTION.CALL_MDI_WAIT("G53 G0 Z0")
        command = "G53 G0 X{:3.4f} Y{:3.4f}".format(x, y)
        ACTION.CALL_MDI_WAIT(command, 10)
 
    def btn_ref_laser_clicked(self):
        #x = float(self.w.lineEdit_laser_x.text())
        #y = float(self.w.lineEdit_laser_y.text())
        if not STATUS.is_metric_mode():
            x = x / 25.4
            y = y / 25.4
        self.add_status("Laser offsets set")
        command = "G10 L20 P0 X{:3.4f} Y{:3.4f}".format(x, y)
        ACTION.CALL_MDI(command)
    
    # tool tab
    def btn_m61_clicked(self):
        checked = self.w.tooloffsetview.get_checked_list()
        if len(checked) > 1:
            self.add_status("Select only 1 tool to load")
        elif checked:
            self.add_status("Loaded tool {}".format(checked[0]))
            ACTION.CALL_MDI("M61 Q{}".format(checked[0]))
        else:
            self.add_status("No tool selected")

    def btn_touchoff_clicked(self):
        if STATUS.get_current_tool() == 0:
            self.add_status("Cannot touchoff with no tool loaded")
            return
        if not STATUS.is_all_homed():
            self.add_status("Must be homed to perform tool touchoff")
            return
        # instantiate dialog box
        sensor = self.w.sender().property('sensor')
        info = "Ensure tooltip is within {} mm of tool sensor and click OK".format(self.w.lineEdit_max_probe.text())
        mess = {'NAME':'MESSAGE', 'ID':sensor, 'MESSAGE':'TOOL TOUCHOFF', 'MORE':info, 'TYPE':'OKCANCEL'}
        ACTION.CALL_DIALOG(mess)
        
    # status tab
    def btn_clear_status_clicked(self):
        STATUS.emit('update-machine-log', None, 'DELETE')

    def btn_save_status_clicked(self):
        text = self.w.machinelog.toPlainText()
        filename = self.w.lbl_clock.text().encode('utf-8')
        filename = 'status_' + filename.replace(' ','_') + '.txt'
        self.add_status("Saving Status file to {}".format(filename))
        with open(filename, 'w') as f:
            f.write(text)

    def btn_dimensions_clicked(self, state):
        self.w.gcodegraphics.show_extents_option = state
        self.w.gcodegraphics.updateGL()

    
    def chk_override_limits(self, state):
        return
        

    def chk_override_limits_checked(self, state):
        if state:
            print("Override limits set")
            ACTION.TOGGLE_LIMITS_OVERRIDE()
        else:
            ACTION.TOGGLE_LIMITS_OVERRIDE()
            print("Override limits not set")

    def chk_run_from_line_checked(self, state):
        if not state:
            self.w.lbl_start_line.setText('1')

    def chk_alpha_mode_clicked(self, state):
        self.w.gcodegraphics.set_alpha_mode(state)

    def chk_inhibit_display_selection_clicked(self, state):
        self.w.gcodegraphics.set_inhibit_selection(state)

    # settings tab
    def chk_use_virtual_changed(self, state):
        if not state:
            self.w.stackedWidget_dro.setCurrentIndex(0)
    
    def btn_zero_axis_cmd(self):
        #con esto miro la posicion de los ejes
        s = linuxcnc.stat()
        s.poll()
        x,y,z = s.actual_position[0],s.actual_position[1],s.actual_position[2]
        key = (self.w.sender().objectName())
        print(key,x,y,z)

        def chk_init_pos(pos, axis):
            msg_axis_error = "Eje %s no esta en posicion" % (axis)
            if axis == 'x':
                if pos >= (int(self.safe_pos_x) - self.safe_pos_offset) and pos <= (int(self.safe_pos_x) + self.safe_pos_offset):
                    return True
                else:
                    return msg_axis_error
            elif axis == 'y':
                if pos >= (int(self.safe_pos_y) - self.safe_pos_offset) and pos <= (int(self.safe_pos_y) + self.safe_pos_offset):
                    return True
                else:
                    return msg_axis_error
            else:
                if pos >= (int(self.safe_pos_z) - self.safe_pos_offset) and pos <= (int(self.safe_pos_z) + self.safe_pos_offset):
                    return True
                else:
                    return msg_axis_error

        if key == 'action_zero_x':
            if chk_init_pos(y,"y") == True and chk_init_pos(z,"z") == True:
                ACTION.CALL_MDI("G1 X%s F1000" % (self.safe_pos_x))
            if chk_init_pos(y,"y") != True:
                self.add_status(chk_init_pos(y,"y"))
            if chk_init_pos(z,"z") != True:
                self.add_status(chk_init_pos(z,"z"))

        elif key == 'action_zero_y':
            if chk_init_pos(z,"z") == True:
                ACTION.CALL_MDI("G1 Y%s F1000" % (self.safe_pos_y))
            else:
                self.add_status(chk_init_pos(z,"z"))

        elif key == 'action_zero_z':
            ACTION.CALL_MDI("G1 Z%s F1000" % (self.safe_pos_z))




        #if key == 'action_zero_x' and y >= (int(self.safe_pos_y) - self.safe_pos_offset) and y <= (int(self.safe_pos_y) + self.safe_pos_offset) and z >= (int(self.safe_pos_z)-self.safe_pos_offset) and z <= (int(self.safe_pos_z)+self.safe_pos_offset):
        #    #ACTION.CALL_MDI("G1 X0 F1000")
        #    ACTION.CALL_MDI("G1 X%s F1000" % (self.safe_pos_x))
        #elif key == 'action_zero_y' and z >= (int(self.safe_pos_z) - self.safe_pos_offset) and z <= (int(self.safe_pos_z) + self.safe_pos_offset):
        #    #ACTION.CALL_MDI("G1 Y0 F1000")
        #    ACTION.CALL_MDI("G1 Y%s F1000" % (self.safe_pos_y))
        #elif key == 'action_zero_z':
        #    #ACTION.CALL_MDI("G1 Z0 F1000")
        #    ACTION.CALL_MDI("G1 Z%s F1000" % (self.safe_pos_z))
            
    #####################
    # THREAD FUNCTIONS #
    #####################

    class MiThread(QThread):
        finished_signal = pyqtSignal()
        def run(self):
            try:
                #print("direccion",super(HandlerClass, self).__init__())
                print dir(self)
                self.msleep(3000)
                for _ in range(0, 10):
                    print("Hola desde el hilo")
                    #super().add_status("CRITICAL - no preference file found, enable preferences in screenoptions widget")
                    self.msleep(1000)

                self.finished_signal.emit()
            except Exception as e:
                print("Error en el hilo:  ",e)
    
    def iniciar_hilo(self):
		#print 'hilo principal iniciado', dir(self)
		# Crear una instancia del hilo
		#self.mi_hilo = self.MiThread()

		# Iniciar el hilo
		#self.mi_hilo.start()
        
        time.sleep(3)
        self.thread.start()

    def master_init_conditions(self, userdata=None):
        #print dir(self)
        #self.add_status("asdasdassad")
        old_len_list = 0
        while True:
            #(userdata('asd'))
            text = self.w.machinelog.toPlainText()
            list_of_messages = text.split('\n')
            current_day = str(date.today()).encode('utf-8') 
            filename = 'log_' + current_day.replace(' ','_') + '.txt'
            contenido = os.listdir(self.messages_log)
            if len(list_of_messages) != old_len_list:
                valor = list_of_messages[-((len(list_of_messages)-old_len_list)+1):]
                if filename in contenido:
                    try:
                        with open(self.messages_log + filename, 'a') as f:
                            for n in valor:
                                f.write(n + '\n')
                            f.close()
                    except Exception as e:
                        print("Error al escribir en el archivo")
                else:
                    try:
                        with open(self.messages_log + filename, 'w') as f:
                            f.write(text)
                            f.close()
                    except Exception as e:
                        print("Error al escribir en el archivo")
                    
            old_len_list = len(list_of_messages)
            unicode_string = text.decode("utf-8")

  
            #chequea si hay errores de rutinas para poder imprimirlos
            for key, value in self.routine_error_messages.items():
                if value:
                    self.h['carga-errors'] = 1


            if self.err_routine == True:
                self.py_control_pins['CTRL_init_master'].set(True)
                time.sleep(0.3)
                # Paso 0 - Condiciones iniciales SETEO DE FLAGS
                if (STATUS.is_auto_mode() == False):
                    # Paso 0 - Apaga flag de control rutina terminada
                    key_1 = 'CTRL_blw_er'
                    if not self.send_pctrl(key_1, False):
                        print('Error Envio de comando flag control - SOPLADO - Paso 0 - No se pudo apagar flag soplado')
                        self.err_routine = False

                    # Paso 1 - Apaga flag de control gantry puede ingresar al ch
                    key_1 = 'CTRL_ch_ce'
                    if not self.send_pctrl(key_1, False):
                        print('Error Envio de comando flag control - OKUMA - Paso 0 - No se pudo apagar flag gantry puede entrar')
                        self.err_routine = False

                # Paso 0 - Condiciones iniciales CARGA
                init_conditions_error_messages = self.check_init_conditions_carga()
                init_conditions_error_messages.insert(0,'Error en condiciones iniciales de carga')
                self.init_conditions_error_messages['carga'] = init_conditions_error_messages[:]
                if len(init_conditions_error_messages) > 1:
                    #pass
                    if self.chk_init_conditions == True:
                        print('\nError en condiciones iniciales de carga')
                        for err in init_conditions_error_messages:
                            print(err)
                else:
                    self.threadLoad = threading.Thread(target=self.load_routine)
                    self.threadLoad.start()
                    
                # Paso 0 - Condiciones iniciales DESCARGA
                init_conditions_error_messages = self.check_init_conditions_descarga()
                init_conditions_error_messages.insert(0,'Error en condiciones iniciales de descarga')
                self.init_conditions_error_messages['descarga'] = init_conditions_error_messages[:]
                if len(init_conditions_error_messages) > 1:
                    #pass
                    if self.chk_init_conditions == True:
                        print('\nError en condiciones iniciales de descarga')
                        for err in init_conditions_error_messages:
                            print(err)
                else:
                    self.threadUnload = threading.Thread(target=self.unload_routine)
                    self.threadUnload.start()
                    

                # Paso 0 - Condiciones iniciales SOPLADOR
                init_conditions_error_messages = self.check_init_conditions_blw()
                init_conditions_error_messages.insert(0,'Error en condiciones iniciales de soplador')
                self.init_conditions_error_messages['soplador'] = init_conditions_error_messages[:]
                if len(init_conditions_error_messages) > 1:
                    for err in init_conditions_error_messages:
                        print(err)
                    #pass
                    #if self.chk_init_conditions == True:
                    #    print('\nError en condiciones iniciales de soplador')
                    #    for err in init_conditions_error_messages:
                    #        print(err)
                else:
                    self.threadBlower = threading.Thread(target=self.blw_routine)
                    self.threadBlower.start()

                
                # Paso 0 - Condiciones iniciales TORNO ENTRAR
                init_conditions_error_messages = self.check_init_conditions_ch_entrar()
                init_conditions_error_messages.insert(0,'Error en condiciones iniciales de torno entrar')
                self.init_conditions_error_messages['torno_entrar'] = init_conditions_error_messages[:]
                if len(init_conditions_error_messages) > 1:
                    #pass
                    if self.chk_init_conditions == True:
                        print('\nError en condiciones iniciales de torno entrar')
                        for err in init_conditions_error_messages:
                            print(err)
                else:
                    self.threadTorno_entrar = threading.Thread(target=self.ch_routine_entrar)
                    self.threadTorno_entrar.start()


                # Paso 0 - Condiciones iniciales TORNO SALIR
                init_conditions_error_messages = self.check_init_conditions_ch_salir()
                init_conditions_error_messages.insert(0,'Error en condiciones iniciales de torno salir')
                self.init_conditions_error_messages['torno_salir'] = init_conditions_error_messages[:]
                if len(init_conditions_error_messages) > 1:
                    #pass
                    if self.chk_init_conditions == True:
                        print('\nError en condiciones iniciales de torno salir')
                        for err in init_conditions_error_messages:
                            print(err)
                else:
                    self.threadTorno_salir = threading.Thread(target=self.ch_routine_salir)
                    self.threadTorno_salir.start()

                # Paso 0 - Condiciones iniciales PATEADOR
                init_conditions_error_messages = self.check_init_conditions_pateador()
                init_conditions_error_messages.insert(0,'Error en condiciones iniciales de pateador')
                self.init_conditions_error_messages['pateador'] = init_conditions_error_messages[:] 
                if len(init_conditions_error_messages) > 1:
                    #pass
                    if self.chk_init_conditions == True:
                        print('\nError en condiciones iniciales de pateador')
                        for err in init_conditions_error_messages:
                            print(err)
                else:
                    self.threadPateador = threading.Thread(target=self.pateador_routine)
                    self.threadPateador.start()


                # Paso 0 - Test thread
                # self.threadPateador = threading.Thread(target=self.pateador_routine)
                # if self.threadPateador.start() ==

                
                self.chk_init_conditions = False
            else:
                self.py_control_pins['CTRL_init_master'].set(False)

    def btn_chk_init_conditions(self):
        self.chk_init_conditions = True
        for key, error_messages_list in self.init_conditions_error_messages.items():
            for n in error_messages_list:
                self.add_status(n)
            self.add_status('--------------------------------------------------------------------------------------')
    
    def btn_reset_master_init(self):
        self.err_routine = True

    def btn_last_cycle(self):
        key = (self.w.sender().objectName())
        if self.py_control_pins[key].get() == False:
            self.py_control_pins[key].set(True)
        else:
            self.py_control_pins[key].set(False)
        #self.py_control_pins['CTRL_end_cycle'].set(True)

    def btn_toggle_ev(self):
        key = (self.w.sender().objectName())
        #self.w["EV_tor_gate_open"].setStyleSheet("color:red")
        print('togle buton', self.py_out_pins[key].get())
        if self.py_out_pins[key].get() == False:
            self.py_out_pins[key].set(True)
            self.w[key].setStyleSheet("color:green")
        else:
            self.py_out_pins[key].set(False)
            self.w[key].setStyleSheet("color:red")

    
# **************************************** XXXX ****************************************
# **************************************** XXXX ****************************************
# **************************************** XXXX ****************************************

 	# ********* rutina - PATEADOR *********
    def pateador_routine(self):
        # Paso 1 - Subir cuna
        key_1 = 'EV_pat_up'
        key_2 = 'EV_pat_down'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - KICKER - Step 1 - Raise cradle' 
            print(msg_error)
            self.routine_error_messages['pateador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 1.1 - Chequea sensor neumatico de cuna arriba
        sen_key = 'SEN_pat_up'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - KICKER - Step 1.1 - Check cradle up sensor' 
            print(msg_error)
            self.routine_error_messages['pateador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 2 - Acciona pateador hacia adelante(patea)
        key_1 = 'EV_pat_frw'
        key_2 = 'EV_pat_bkw'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - KICKER - Step 2 - Actuate kicker forward'
            print(msg_error)
            self.routine_error_messages['pateador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 2.1 - Chequea sensor neumatico pateador accionado(adelante)
        sen_key = 'SEN_pat_frw'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - KICKER - Step 2.1 - Check kicker forward sensor'
            print(msg_error)
            self.routine_error_messages['pateador'].append(msg_error)
            self.err_routine = False
            return False

        time.sleep(2)

        # Paso 3 - Acciona pateador hacia atras
        key_1 = 'EV_pat_bkw'
        key_2 = 'EV_pat_frw'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - KICKER - Step 3 - Actuate kicker backward'
            print(msg_error)
            self.routine_error_messages['pateador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 3.1 - Chequea sensor neumatico pateador atras
        sen_key = 'SEN_pat_bkw'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - KICKER - Step 3.1 - Check kicker backward sensor'
            print(msg_error)
            self.routine_error_messages['pateador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 4 - Chequea sensor de presencia de cupla(que no haya)
        sen_key = 'SEN_pat_pc'
        if not self.wait_for_not_sen_common_flag(sen_key):
            msg_error = 'Optical Sensor Error - KICKER - Step 4 - Coupling present'
            print(msg_error)
            self.routine_error_messages['pateador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 5 - Bajar cuna
        key_1 = 'EV_pat_down'
        key_2 = 'EV_pat_up'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - KICKER - Step 5 - Lower cradle'
            print(msg_error)
            self.routine_error_messages['pateador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 5.1 - Chequea sensor neumatico de cuna abajo
        sen_key = 'SEN_pat_down'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - KICKER - Step 5.1 - Check cradle down sensor'
            print(msg_error)
            self.routine_error_messages['pateador'].append(msg_error)
            self.err_routine = False
            return False

        return True

    # ********* rutina - OKUMA SALIR *********
    def ch_routine_salir(self):
        # Step 1 - Apaga flag de control gantry puede ingresar
        key_1 = 'CTRL_ch_ce'
        if not self.send_pctrl(key_1, False):
            msg_error = 'Control Flag Command Error - OKUMA SALIR - Step 1 - Gantry can enter turned off'
            print(msg_error)
            self.routine_error_messages['torno_salir'].append(msg_error)
            self.err_routine = False
            return False
            
        # Step 2 - Cerrar puerta techo okuma
        key_1 = 'EV_tor_gate_closed'
        key_2 = 'EV_tor_gate_open'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - OKUMA SALIR - Step 2 - Close Okuma ceiling door'
            print(msg_error)
            self.routine_error_messages['torno_salir'].append(msg_error)
            self.err_routine = False
            return False
            
        # Step 2.1 - Chequear sensor neumatico puerta techo cerrada
        sen_key = 'SEN_tor_gate_closed'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - OKUMA SALIR - Step 2.1 - Check closed door sensor'
            print(msg_error)
            self.routine_error_messages['torno_salir'].append(msg_error)
            self.err_routine = False
            return False
            
        ## Step 3 - Cycle start en 1
        #key_1 = 'RI_tor_cs'
        #if not self.send_pneumatic(key_1, True):
        #    msg_error = 'Signal Command Error - OKUMA SALIR - Step 3 - Could not turn on cycle start'
        #    print(msg_error)
        #    self.routine_error_messages['torno_salir'].append(msg_error)
        #    self.err_routine = False
        #    return False
        #    
        #time.sleep(1)

        ## Step 4 - Cycle start en 0
        #key_1 = 'RI_tor_cs'
        #if not self.send_pneumatic(key_1, False):
        #    msg_error = 'Signal Command Error - OKUMA SALIR - Step 4 - Could not turn off cycle start'
        #    print(msg_error)
        #    self.routine_error_messages['torno_salir'].append(msg_error)
        #    self.err_routine = False
        #    return False

        #time.sleep(1)


        #if (hal.get_value('RI_tor_m180_confirm') == True and hal.get_value('RI_tor_m181_confirm') == False and hal.get_value('RI_tor_spare') == False) or 
        #    (hal.get_value('RI_tor_m180_confirm') == False and hal.get_value('RI_tor_m181_confirm') == True and hal.get_value('RI_tor_spare') == True):
        #    # Step 5 - request answer en 1 
        #    key_1 = 'RI_tor_mfin'
        #    if not self.send_pneumatic(key_1, True):
        #        msg_error = 'Signal Command Error - OKUMA SALIR - Step 3 - Could not turn on cycle start'
        #        print(msg_error)
        #        self.routine_error_messages['torno_salir'].append(msg_error)
        #        self.err_routine = False
        #        return False

        #    # Step 5 - request answer en 0 
        #    key_1 = 'RI_tor_mfin'
        #    if not self.send_pneumatic(key_1, True):
        #        msg_error = 'Signal Command Error - OKUMA SALIR - Step 3 - Could not turn of cycle start'
        #        print(msg_error)
        #        self.routine_error_messages['torno_salir'].append(msg_error)
        #        self.err_routine = False
        #        return False

        #else:
        #    msg_error = 'Spare no coincide con m180/m181'
        #    print(msg_error)
        #    self.routine_error_messages['torno_salir'].append(msg_error)
        #    self.err_routine = False
                
        return True

	# ********* rutina - OKUMA ENTRAR *********
    def ch_routine_entrar(self):
        # Paso 1 - cycle start = 0
        sen_key = 'RI_tor_cs'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Signal Error - OKUMA ENTER - Step 1 - Checking cycle start off'
            print(msg_error)
            self.routine_error_messages['torno_entrar'].append(msg_error)
            self.err_routine = False
            return False


        # Paso 1.2 - MFIN = 0, sino error
        key_1 = 'RI_tor_mfin'
        if not self.send_pneumatic(key_1, False):
            msg_error = 'Pneumatic Command Error - OKUMA ENTER - Step 1.2 - request answer off'
            print(msg_error)
            self.routine_error_messages['torno_entrar'].append(msg_error)
            self.err_routine = False
            return False


        # Paso 1.3 - LOADER SYSTEM LINK/AUTO MODE (salida del Gantry que indica que esta en automatico) = 1, sino error
        #en todas las rutinas se chequea que gantry este en automatico y si esta en automatico ya prende la salida de system link


        # Paso 1.4 - ROBOT/LOADER ALARM (salida NC del Gantry que indica que esta en alarma) = 1, sino error
        #aca el gantry deberia ponerla en 1 cuando inicia el programa en automatico y cuando saltan los m2 por errores que la apague
        


        # Paso 2 - Chequea senal de Robot out of machine = 1 (que gantry esta afuera del okuma)
        # ROBOT/LOADER OUT OF MACHINE AREA
        #aca deberiamos prender esta senal cuando este en safe pos el gantry
        sen_key = 'RI_tor_ofm'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Signal Error - OKUMA ENTER - Step 2 - Checking robot out of machine is 1'
            print(msg_error)
            self.routine_error_messages['torno_entrar'].append(msg_error)
            self.err_routine = False
            return False


        # Paso 3 - Abrir puerta techo okuma
        key_1 = 'EV_tor_gate_open'
        key_2 = 'EV_tor_gate_closed'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - OKUMA ENTER - Step 3 - Opening roof door'
            print(msg_error)
            self.routine_error_messages['torno_entrar'].append(msg_error)
            self.err_routine = False
            return False
        

        # Paso 3.1 - Chequea sensor neumatico puerta techo abierta
        sen_key = 'SEN_tor_gate_open'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - OKUMA ENTER - Step 3.1 - Checking open door sensor'
            print(msg_error)
            self.routine_error_messages['torno_entrar'].append(msg_error)
            self.err_routine = False
            return False

        
        ## Paso 3.2 - orienta plato
        #key_1 = 'RI_tor_so1'
        #if not self.send_pneumatic(key_1, False):
        #    msg_error = 'Pneumatic Command Error - OKUMA ENTER - Step 1.2 - orientar plato'
        #    print(msg_error)
        #    self.routine_error_messages['torno_entrar'].append(msg_error)
        #    self.err_routine = False
        #    return False

        #no espera a ver plato orientado para no perder tiempo, que lo mire el gantry cuando entra
        

        # Paso 4 - Prende flag de control gantry puede ingresar
        key_1 = 'CTRL_ch_ce'
        if not self.send_pctrl(key_1, True):
            msg_error = 'Control Flag Command Error - OKUMA ENTER - Step 4 - Gantry can enter flag on'
            print(msg_error)
            self.routine_error_messages['torno_entrar'].append(msg_error)
            self.err_routine = False
            return False
        

        return True

	# ********* rutina - SOPLADO *********
    def blw_routine(self):
        # Paso 1 - Chequea sensor neumatico puerta abierta
        sen_key = 'SEN_blw_open'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - BLOWING - Step 1 - Checking open door sensor for blowing'
            print(msg_error)
            self.routine_error_messages['soplador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 2 - Chequea sensor cupla presente
        sen_key = 'SEN_blw_pc'
        #wait_for_not_sen_flag # creo que tengo que usar esta
        if not self.wait_for_not_sen_common_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - BLOWING - Step 2 - Checking presence sensor'
            print(msg_error)
            self.routine_error_messages['soplador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 3 - Cerrar puerta soplador
        key_1 = 'EV_blw_close_cobertor'
        key_2 = 'EV_blw_open_cobertor'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - BLOWING - Step 3 - Lower vertical discharge'
            print(msg_error)
            self.routine_error_messages['soplador'].append(msg_error)
            self.err_routine = False
            return False


        # Paso 3.1 - Chequea sensor neumatico puerta cerrada
        sen_key = 'SEN_blw_closed'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - BLOWING - Step 3.1 - Checking closed door sensor for blowing'
            print(msg_error)
            self.routine_error_messages['soplador'].append(msg_error)
            self.err_routine = False
            return False


        # Paso 4 - Accionar soplador
        key_1 = 'EV_blw_on'
        if not self.send_pneumatic(key_1, True):
            msg_error = 'Pneumatic Command Error - BLOWING - Step 4 - Activate blower'
            print(msg_error)
            self.routine_error_messages['soplador'].append(msg_error)
            self.err_routine = False
            return False

        time.sleep(3)

        # Paso 5 - Desactiva soplador
        key_1 = 'EV_blw_on'
        if not self.send_pneumatic(key_1, False):
            msg_error = 'Pneumatic Command Error - BLOWING - Step 5 - Deactivate blower'
            print(msg_error)
            self.routine_error_messages['soplador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 6 - Abrir puerta soplador
        key_1 = 'EV_blw_open_cobertor'
        key_2 = 'EV_blw_close_cobertor'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - BLOWING - Step 6 - Open cobertor'
            print(msg_error)
            self.routine_error_messages['soplador'].append(msg_error)
            self.err_routine = False
            return False
        
        # Paso 6.1 - Chequea sensor neumatico puerta abierta
        sen_key = 'SEN_blw_open'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - BLOWING - Step 6.1 - Checking open door sensor for blowing'
            print(msg_error)
            self.routine_error_messages['soplador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 7 - Prende flag de control rutina terminada
        key_1 = 'CTRL_blw_er'
        if not self.send_pctrl(key_1, True):
            msg_error = 'Control Flag Command Error - BLOWING - Step 7 - Blowing routine finished'
            print(msg_error)
            self.routine_error_messages['soplador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 8 - Espera accionar soplado en 0
        sen_key = 'CTRL_blw_sr'
        if not self.wait_for_ctrl_flag(sen_key):
            msg_error = 'Control Flag Error - BLOWING - Step 8 - Wait for start flag blower routine off'
            print(msg_error)
            self.routine_error_messages['soplador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 9 - Chequea sensor cupla no presente
        sen_key = 'SEN_blw_pc'
        if not self.wait_for_not_sen_common_flag(sen_key):
            msg_error = 'Presence Sensor Error - BLOWING - Step 9 - Presence coupling sensor active in blower'
            print(msg_error)
            self.routine_error_messages['soplador'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 10 - Apaga flag de control rutina terminada
        key_1 = 'CTRL_blw_er'
        if not self.send_pctrl(key_1, False):
            msg_error = 'Control Flag Command Error - BLOWING - Step 10 - Failed to turn off blowing flag'
            print(msg_error)
            self.routine_error_messages['soplador'].append(msg_error)
            self.err_routine = False
            return False

        return True

    # ********* rutina - DESCARGA *********
    def unload_routine(self):
        # Paso 0 - Prende flag de presencia de cupla
        self.flag_bd_pc = True

        # Paso 1 - Bajar vertical de descarga
        key_1 = 'EV_bd_down'
        key_2 = 'EV_bd_up'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - UNLOAD - Step 1 - Lower vertical discharge'
            print(msg_error)
            self.routine_error_messages['descarga'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 2 - Chequea sensor descarga llena
        sen_key = self.flag_bd_pc
        if not self.wait_for_not_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - UNLOAD - Step 2 - Cup did not pass the discharge sensor'
            print(msg_error)
            self.routine_error_messages['descarga'].append(msg_error)
            self.err_routine = False
            return False
            
        # Paso 1.1 - Chequea sensor neumatico
        sen_key = 'SEN_bd_down'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - UNLOAD - Step 1.1 - Checking vertical sensor'
            print(msg_error)
            self.routine_error_messages['descarga'].append(msg_error)
            self.err_routine = False
            return False


        # Paso 3 - subir vertical de descarga
        key_1 = 'EV_bd_up'
        key_2 = 'EV_bd_down'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - UNLOAD - Step 3 - Raise vertical discharge'
            print(msg_error)
            self.routine_error_messages['descarga'].append(msg_error)
            self.err_routine = False
            return False
            
        # Paso 3.1 - Chequea sensor neumatico
        sen_key = 'SEN_bd_up'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - UNLOAD - Step 3.1 - Checking upper vertical sensor'
            print(msg_error)
            self.routine_error_messages['descarga'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 4 - Chequea cupla no presente en vertical descarga
        sen_key = 'SEN_bd_pc'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Presence Sensor Error - UNLOAD - Step 4 - Cup present in vertical discharge'
            print(msg_error)
            self.routine_error_messages['descarga'].append(msg_error)
            self.err_routine = False
            return False
        
        return True

	# ********* rutina - CARGA *********
    def load_routine(self):
        print "load thread activo"
        # Paso 1 - Bajar vertical de carga
        key_1 = 'EV_bc_down'
        key_2 = 'EV_bc_up'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - LOADING - Step 1 - Lower vertical loading'
            print(msg_error)
            self.routine_error_messages['carga'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 1.1 - Chequea sensor neumatico
        sen_key = 'SEN_bc_down'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - LOADING - Step 1.1 - Checking vertical sensor'
            print(msg_error)
            self.routine_error_messages['carga'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 2 - Segregador vuelca
        key_1 = 'EV_seg_overturn'
        key_2 = 'EV_seg_idle'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - LOADING - Step 2 - Overturn segregator'
            print(msg_error)
            self.routine_error_messages['carga'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 2.1 - Chequea sensor segregador volcado
        sen_key = 'SEN_seg_overturn'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - LOADING - Step 2.1 - Checking segregator overturn sensor'
            print(msg_error)
            self.routine_error_messages['carga'].append(msg_error)
            self.err_routine = False
            return False

        time.sleep(3)	#espera que se vuelque la cupla
        
        # Paso 3 - Subir vertical de carga
        key_1 = 'EV_bc_up'
        key_2 = 'EV_bc_down'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - LOADING - Step 3 - Raise vertical loading'
            print(msg_error)
            self.routine_error_messages['carga'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 3.1 - Chequea sensor vertical carga
        sen_key = 'SEN_seg_overturn'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - LOADING - Step 3.1 - Checking upper vertical sensor'
            print(msg_error)
            self.routine_error_messages['carga'].append(msg_error)
            self.err_routine = False
            return False

            
        # Paso 4 - Chequea cupla en vertical carga
        sen_key = 'SEN_bc_pc'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Presence Sensor Error - LOADING - Step 4 - Checking cuping presence sensor in vertical loading'
            print(msg_error)
            self.routine_error_messages['carga'].append(msg_error)
            self.err_routine = False
            return False

            
        # Paso 5 - Vuelve segregador a posicion de carga(idle)
        key_1 = 'EV_seg_idle'
        key_2 = 'EV_seg_overturn'
        if not self.send_pneumatic(key_1, True, key_2, False):
            msg_error = 'Pneumatic Command Error - LOADING - Step 5 - Return to loading position (idle)'
            print(msg_error)
            self.routine_error_messages['carga'].append(msg_error)
            self.err_routine = False
            return False

        # Paso 5.1 - Chequea sensor de segregador posicion carga(idle)
        sen_key = 'SEN_seg_idle'
        if not self.wait_for_sen_flag(sen_key):
            msg_error = 'Pneumatic Sensor Error - LOADING - Step 5.1 - Checking segregator position sensor (idle)'
            print(msg_error)
            self.routine_error_messages['carga'].append(msg_error)
            self.err_routine = False
            return False


        return True
				


    # ********* condiciones iniciales - PATEADOR *********
    def check_init_conditions_pateador(self):
		anular = True
		s = linuxcnc.stat() # create a connection to the status channel
    		s.poll() # get current values
		error_messages = []
		# Paso 0 - Chequear condiciones iniciales - Todos los valores deben ser True par que empiece la rutina
		init_flags = [
			(self.threadPateador.is_alive() == False, 'Rutina ya ejecutandose'),			
			(hal.get_value('SEN_pat_pc') == True, 'Cupla no presente en pateador'),
            (hal.get_value('SEN_pat_down') == True, 'Cuna no esta abajo'),
            (hal.get_value('SEN_pat_bkw') == True, 'Pateador no retraido'),
			(s.task_mode == 2, 'Gantry no esta en estado 2 (programa en automatico)'),
      		(s.task_paused == 0, 'Pausa esta activa'),
            #(flag de que se puede patear == True, 'flag de pateo no activo'),
            (self.err_routine == True, 'Error en rutina previo'),
      		#(anular == False, 'anulada activa'),
            (hal.get_value('RI_tor_sl_confirm') == True, 'Senal de system link del torno no esta prendida'),
		]

		for flag, error in init_flags:
			if flag == False:
				error_messages.append(error)

		return error_messages

	# ********* condiciones iniciales - OKUMA SALIR *********
    def check_init_conditions_ch_salir(self):
		anular = True
		s = linuxcnc.stat() # create a connection to the status channel
    		s.poll() # get current values
		error_messages = []
		# Paso 0 - Chequear condiciones iniciales - Todos los valores deben ser True par que empiece la rutina
		init_flags = [
		    (self.threadTorno_salir.is_alive() == False, 'Rutina ya ejecutandose'),
			(hal.get_value('RI_tor_ep_confirm') == True, 'Torno no termino programa'), #PROGRAM END=1 (esta es la que GC describe como CYCLE COMPLETE en 1)
   			
            (hal.get_value('RI_tor_alarm_confirm') == True, 'Torno se encuentra en alarma'), #NC ALARM=1
            #tiene sentido???, aunque el torno este en alarma, conviene que el Gantry Salga....
            #ts: no si chequiamos mhp(machine home p)

			(hal.get_value('SEN_tor_gate_open') == True, 'Puerta techo no esta abierta'), # condicion1
			(self.py_out_pins['RI_tor_ofm'].get() == True, 'Robot dentro de okuma'), #condicion2
            #solo se ejecuta si la puerta esta abierta y el robot esta fuera de la maquina son condiciones 1 y 2
            #para que no entre en un loop repetitivo
            #aunque por ejemplo al iniciar el sistema se puede dar que robot esta afuera y la puerta esta abierta...
            #habria que poner como 3er condicion que el flag de que el robot puede ingresar este en 1
            #con eso aseguramos que venga de la rutina Okuma Entrar, total en el paso 1 lo baja a ese flag
            #ts: pondria como condicion inicial en el codigo g para que el gantry arranque con la puerta cerrada
      		(s.task_mode == 2, 'Gantry no esta en estado 2 (programa en automatico)'),
      		(s.task_paused == 0, 'Pausa esta activa'),
            (self.err_routine == True, 'Error en rutina previo'),
      		#(anular == False, 'anulada activa'),
            (hal.get_value('RI_tor_sl_confirm') == True, 'Senal de system link del torno no esta prendida'),
            (self.py_control_pins['CTRL_ch_ce'].get() == True, 'Flag de gantry puede ingresar al okuma esta apagado'),
      
		]

		for flag, error in init_flags:
			if flag == False:
				error_messages.append(error)

		return error_messages

	# ********* condiciones iniciales - OKUMA ENTRAR *********
    def check_init_conditions_ch_entrar(self):
		anular = True
		s = linuxcnc.stat() # create a connection to the status channel
    		s.poll() # get current values
		error_messages = []
		# Paso 0 - Chequear condiciones iniciales - Todos los valores deben ser True par que empiece la rutina
		init_flags = [
			(self.threadTorno_entrar.is_alive() == False, 'Rutina ya ejecutandose'),
			(hal.get_value('RI_tor_ep_confirm') == True, 'Torno no termino programa'), #PROGRAM END=1 (esta es la que GC describe como CYCLE COMPLETE en 1)
   			(hal.get_value('RI_tor_alarm_confirm') == False, 'Torno se encuentra en alarma'), #NC ALARM=1
      		(hal.get_value('RI_tor_home_confirm') == True, 'Torno no se encuentra en home'), #MACHINE HOME POSITION=1
			(hal.get_value('SEN_tor_gate_closed') == True, 'Puerta techo no esta cerrada'),	
      		(s.task_mode == 2, 'Gantry no esta en estado 2 (programa en automatico)'),
      		(s.task_paused == 0, 'Pausa esta activa'),
            (self.err_routine == True, 'Error en rutina previo'),
      		#(anular == False, 'anulada activa'),
            (hal.get_value('RI_tor_cstop_confirm') == True, 'Senal de cycle stop prendida'),
            (hal.get_value('RI_tor_m180_confirm') == False, 'Senal m180 del torno prendida'),
            (hal.get_value('RI_tor_m181_confirm') == False, 'Senal m181 del torno prendida'),
            (hal.get_value('RI_tor_sl_confirm') == True, 'Senal de system link del torno no esta prendida'),
                #SYSTEM LINK MODE = 1 hay q chequearlo en todas las rutinas
      
		]

		for flag, error in init_flags:
			if flag == False:
				error_messages.append(error)

		return error_messages

	# ********* condiciones iniciales - SOPLADO *********
    def check_init_conditions_blw(self):
		anular = True
		s = linuxcnc.stat() # create a connection to the status channel
    		s.poll() # get current values
		error_messages = []
		# Paso 0 - Chequear condiciones iniciales - Todos los valores deben ser True par que empiece la rutina
		init_flags = [
			(self.threadBlower.is_alive() == False, 'Rutina ya ejecutandose'),
			(self.py_control_pins['CTRL_blw_sr'].get() == True, 'Flag de comenzar rutina soplado no esta encendido'),	
   			(self.py_control_pins['CTRL_blw_er'].get() == False, 'Flag de finalizacion de rutina de soplado no esta apagado'),
      		(self.py_control_pins['CTRL_blw_ogr'].get() == False, 'Gantry no debe estar ejecutando rutina de soplador'),
      		(s.task_mode == 2, 'Gantry no esta en estado 2 (programa en automatico)'),
      		(s.task_paused == 0, 'Pausa esta activa'),
            (self.err_routine == True, 'Error en rutina previo'),
      		#(anular == False, 'anulada activa'),
            #(hal.get_value('RI_tor_sl_confirm') == True, 'Senal de system link del torno no esta prendida'),
      
		]

		for flag, error in init_flags:
			if flag == False:
				error_messages.append(error)

		return error_messages

	# ********* condiciones iniciales - DESCARGA *********
    def check_init_conditions_descarga(self):
        anular = True
        s = linuxcnc.stat() # create a connection to the status channel
        s.poll() # get current values
        error_messages = []
        # Paso 0 - Chequear condiciones iniciales - Todos los valores deben ser True par que empiece la rutina
        if self.py_control_pins['CTRL_ch_od'].get() == False:
            init_flags = [
                (self.threadUnload.is_alive() == False, 'Rutina ya ejecutandose'),
                (hal.get_value('SEN_bd_up') == True, 'Piston de descarga no esta arriba'),	
                (hal.get_value('SEN_bd_pc') == False, 'Cupla no presente en descarga'),
                (hal.get_value('SEN_bd_full') == True, 'Bancal descarga lleno'),
                (self.py_control_pins['CTRL_bd_ogr'].get() == False, 'Gantry no debe estar ejecutando rutina de descarga'),
                (s.task_mode == 2, 'Gantry no esta en estado 2 (programa en automatico)'),
                (s.task_paused == 0, 'Pausa esta activa'),
                (self.err_routine == True, 'Error en rutina previo'),
                #(anular == False, 'anulada activa'),
                (hal.get_value('RI_tor_sl_confirm') == True, 'Senal de system link del torno no esta prendida'),
            ]
        else:
            init_flags = [
                (self.threadUnload.is_alive() == False, 'Rutina ya ejecutandose'),
                (hal.get_value('SEN_bd_up') == True, 'Piston de descarga no esta arriba'),	
                (hal.get_value('SEN_bd_pc') == False, 'Cupla no presente en descarga'),
                (hal.get_value('SEN_bd_full') == True, 'Bancal descarga lleno'),
                (self.py_control_pins['CTRL_bd_ogr'].get() == False, 'Gantry no debe estar ejecutando rutina de descarga'),
                (s.task_mode == 2, 'Gantry no esta en estado 2 (programa en automatico)'),
                (s.task_paused == 0, 'Pausa esta activa'),
                (self.err_routine == True, 'Error en rutina previo'),
                #(anular == False, 'anulada activa'),
                (hal.get_value('SEN_bd_bkw') == True, 'Piston de descarga adelante'),
                (hal.get_value('RI_tor_sl_confirm') == True, 'Senal de system link del torno no esta prendida'),
            ]


        for flag, error in init_flags:
            if flag == False:
                error_messages.append(error)

        return error_messages
			
    # ********* condiciones iniciales - CARGA *********
    def check_init_conditions_carga(self):
        anular = True
        s = linuxcnc.stat() # create a connection to the status channel
        s.poll() # get current values
        error_messages = []
        # Paso 0 - Chequear condiciones iniciales - Todos los valores deben ser True par que empiece la rutina
        if self.py_control_pins['CTRL_ch_od'].get() == False:
            init_flags = [
                (self.threadLoad.is_alive() == False, 'Rutina ya ejecutandose'),
                (hal.get_value('SEN_seg_idle') == True, 'Segregador no presente del lado carga'),	
                (hal.get_value('SEN_bc_up') == True, 'Piston de carga no esta arriba'),				
                (hal.get_value('SEN_seg_pc') == True, 'Cupla no presente en segregador'),					
                (hal.get_value('SEN_bc_pc') == False, 'Cupla presente en carga'),
                (self.py_control_pins['CTRL_bc_ogr'].get() == False, 'Gantry no debe estar ejecutando rutina de carga'),
                (s.task_mode == 2, 'Gantry no esta en estado 2 (programa en automatico)'),
                (s.task_paused == 0, 'Pausa esta activa'),
                (self.err_routine == True, 'Error en rutina previo'),
                #(anular == False, 'anulada activa'),
                (hal.get_value('RI_tor_sl_confirm') == True, 'Senal de system link del torno no esta prendida'),
            ]
        else:
            init_flags = [
                (self.threadLoad.is_alive() == False, 'Rutina ya ejecutandose'),
                (hal.get_value('SEN_seg_idle') == True, 'Segregador no presente del lado carga'),	
                (hal.get_value('SEN_bc_up') == True, 'Piston de carga no esta arriba'),				
                (hal.get_value('SEN_seg_pc') == True, 'Cupla no presente en segregador'),					
                (hal.get_value('SEN_bc_pc') == True, 'Cupla presente en carga'),
                (self.py_control_pins['CTRL_bc_ogr'].get() == False, 'Gantry no debe estar ejecutando rutina de carga'),
                (s.task_mode == 2, 'Gantry no esta en estado 2 (programa en automatico)'),
                (s.task_paused == 0, 'Pausa esta activa'),
                (hal.get_value('SEN_bc_bkw') == True, 'Piston de carga adelante'),
                (self.err_routine == True, 'Error en rutina previo'),
                #(anular == False, 'anulada activa'),
                (hal.get_value('RI_tor_sl_confirm') == True, 'Senal de system link del torno no esta prendida'),
            ]

        for flag, error in init_flags:
            if flag == False:
                error_messages.append(error)

        return error_messages
	

# **************************************** XXXX ****************************************
# **************************************** XXXX ****************************************
# **************************************** XXXX ****************************************

    #####################
    # COMMANDS FUNCTIONS #
    #####################

    #check ctrl flags cmd
    def wait_for_ctrl_flag(self, sen_key):
		sen_check = self.py_control_pins[sen_key].get()
		start_time = datetime.datetime.now()
		while not sen_check:
			sen_check = self.py_control_pins[sen_key].get()
			elapsed_time = (datetime.datetime.now() - start_time).total_seconds()
			if elapsed_time >= self.TIMEOUT_PNEUMATIC:
				return False
			time.sleep(self.wait_time)	
		return True
    

    #check sensors neumatic cmd
    def wait_for_sen_flag(self, sen_key):
        #print('el pin es',(hal.get_value('SEN_bd_down')))
        sen_check = hal.get_value(sen_key)
        start_time = datetime.datetime.now()
        while not sen_check:
            sen_check = hal.get_value(sen_key)
            elapsed_time = (datetime.datetime.now() - start_time).total_seconds()
            if elapsed_time >= self.TIMEOUT_PNEUMATIC:
                return False
            time.sleep(self.wait_time)
        return True


    #check sensors n/c neumatic cmd
    def wait_for_not_sen_common_flag(self, sen_key):
        sen_check = hal.get_value(sen_key)
        start_time = datetime.datetime.now()
        while sen_check:
            sen_check = hal.get_value(sen_key)
            elapsed_time = (datetime.datetime.now() - start_time).total_seconds()
            if elapsed_time >= self.TIMEOUT_PNEUMATIC:
                return False
            time.sleep(self.wait_time)	
        return True
		
	
	#check sensor 'SEN_bd_pc' neumatic cmd	
    def wait_for_not_sen_flag(self, sen_key):
		sen_check = sen_key
		start_time = datetime.datetime.now()
		while sen_check:
			sen_check = self.flag_bd_pc
			elapsed_time = (datetime.datetime.now() - start_time).total_seconds()
			if elapsed_time >= self.TIMEOUT_PNEUMATIC:
				return False
			time.sleep(self.wait_time)
		return True	
			
	#send neumatic commands
    def send_pneumatic(self, key, bool_value, second_key=None, second_bool_value=None):
		try:
			self.py_out_pins[key].set(bool_value)
			time.sleep(0.1)
			if second_key:
				self.py_out_pins[second_key].set(second_bool_value)
			#print 'comando enviado exitoso'
			return True
		except:
			return False
	
	#send control commands
    def send_pctrl(self, key, bool_value, second_key=None, second_bool_value=None):
		try:
			self.py_control_pins[key].set(bool_value)
			time.sleep(0.1)
			if second_key:
				self.py_control_pins[second_key].set(second_bool_value)
			#print 'comando enviado exitoso'
			return True
		except:
			return False

    #####################
    # GENERAL FUNCTIONS #
    #####################
    def load_code(self, fname):
        if fname == "":
            ACTION.OPEN_PROGRAM(self.program_empty)
            ACTION.SET_MANUAL_MODE()
        else:
            if fname is None: return
            filename, file_extension = os.path.splitext(fname)
            if not fname.endswith(".html"):
                if not (INFO.program_extension_valid(fname)):
                    self.add_status("Unknown or invalid filename extension {}".format(file_extension))
                    return
                self.w.cmb_gcode_history.addItem(fname)
                self.w.cmb_gcode_history.setCurrentIndex(self.w.cmb_gcode_history.count() - 1)
                ACTION.OPEN_PROGRAM(fname)
                self.add_status("Loaded program file : {}".format(fname))
                self.w.main_tab_widget.setCurrentIndex(TAB_MAIN)
            elif fname.endswith(".html"):
                self.web_view.load(QtCore.QUrl.fromLocalFile(fname))
                self.add_status("Loaded HTML file : {}".format(fname))
                self.w.main_tab_widget.setCurrentIndex(TAB_SETUP)
                self.w.btn_setup.setChecked(True)
            else:
                self.add_status("Unknown or invalid filename")

    def disable_spindle_pause(self):
        self.h['eoffset_count'] = 0
        #if self.w.spindle_pause.isChecked():
        #    self.w.spindle_pause.setChecked(False)

    def iniciar_cliente(self,largo_bruto):
        cliente = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        cliente.connect((self.ip_okuma, 8000))

        while True:
            #manda mensaje
            mensaje = str(largo_bruto)
            cliente.send(mensaje.encode())

            #recibe respuesta
            data = cliente.recv(1024)
            print("sevidor dice",data.decode())

            #aqui debo poner para que el mensaje se imprima por pantalla
            if data == "ok":
                print("valor reemplazado exitosamente")
                cliente.close()
                print("conexion cerrada")
                return True

            else:
                print("valor no pudo ser reemplazado en programa de torno")
                cliente.close()
                print("conexion cerrada")
                self.add_status('Valor no pudo ser reemplazado en programa de torno,conexion cerrada.')
                return False


# *************************************************************************
# ******************************* CALCULOS  *******************************
# *************************************************************************  
        
    #boton cargar programa
    def btn_send_cupla_params(self):
        changed = False
        cuple_inputs_dict = {
        'diametro_bruto': self.w.lineEdit_diametro_bruto.text(),
        'diametro_torneado': self.w.lineEdit_diametro_torneado.text(),
        'diametro_interno': self.w.lineEdit_diametro_interno.text(),
        'largo_bruto': self.w.lineEdit_largo_bruto.text(),
        'largo_op10': self.w.lineEdit_largo_op10.text(),
        'largo_torneado': self.w.lineEdit_largo_op20.text(),
        'd_bruto_altura_ps': 0,
        'd_torneado_altura_ps': 0,
        'd_bruto_altura_cd': 0,
        'd_torneado_altura_cd': 0,
        }

        try:		
            #if float(cuple_inputs_dict['diametro_torneado']) >= 75:
            cuple_inputs_dict['d_bruto_altura_ps'] = math.sin(math.acos(50 / (12.5 + float(cuple_inputs_dict['diametro_bruto']) / 2))) * (12.5 + float(cuple_inputs_dict['diametro_bruto']) / 2)
            cuple_inputs_dict['d_torneado_altura_ps'] = math.sin(math.acos(50 / (12.5 + float(cuple_inputs_dict['diametro_torneado']) / 2))) * (12.5 + float(cuple_inputs_dict['diametro_torneado']) / 2)
            
            print ('el valor del calculo bruto altura ps:',cuple_inputs_dict['d_bruto_altura_ps'])
            print ('el valor del calculo torneado altura ps:',cuple_inputs_dict['d_torneado_altura_ps'])		
            
            #testeado, da bien la formula
            cuple_inputs_dict['d_bruto_altura_cd'] = math.sin(math.radians(55)) * (float(cuple_inputs_dict['diametro_bruto']) / 2) + math.tan(math.radians(35)) * math.cos(math.radians(55)) * (float(cuple_inputs_dict['diametro_bruto']) / 2)
            cuple_inputs_dict['d_torneado_altura_cd'] = math.sin(math.radians(55)) * (float(cuple_inputs_dict['diametro_torneado']) / 2) + math.tan(math.radians(35)) * math.cos(math.radians(55)) * (float(cuple_inputs_dict['diametro_torneado']) / 2)
            
            print ('el valor del calculo CD bruto:',cuple_inputs_dict['d_bruto_altura_cd'])
            print ('el valor del calculo CD torneado:',cuple_inputs_dict['d_torneado_altura_cd'])
        except:
            self.add_status('Valor invalido, no se puede calcular.')
            print('valor invalido, no se puede calcular')
            return

        try:
            # Leer el archivo
            if self.py_control_pins['CTRL_ch_od'].get() == False:
                    
                with open(self.program_not_od, 'r') as file:
                    lines = file.readlines()
                    print lines
                
                # Reemplazar los valores en cada linea
                for i in range(len(lines)):
                    line = lines[i].strip()
                    for key, value in cuple_inputs_dict.iteritems():
                        print key, value
                        if '<_{0}>= '.format(key) in line:
                            lines[i] = line.replace('<_{0}>= {1}'.format(key, line.split("=")[1].strip()), '<_{0}>= {1}'.format(key, str(value))) + '\n'
                            break

                # Escribir las lineas modificadas en el archivo
                with open(self.program_not_od, 'w') as file:
                    file.writelines(lines)
                    changed = True

            else:
                with open(self.program_od, 'r') as file:
                    lines = file.readlines()
                    print lines

                # Reemplazar los valores en cada linea
                for i in range(len(lines)):
                    line = lines[i].strip()
                    for key, value in cuple_inputs_dict.iteritems():
                        print key, value
                        if '<_{0}>= '.format(key) in line:
                            lines[i] = line.replace('<_{0}>= {1}'.format(key, line.split("=")[1].strip()), '<_{0}>= {1}'.format(key, str(value))) + '\n'
                            break

                # Escribir las lineas modificadas en el archivo
                with open(self.program_od, 'w') as file:
                    file.writelines(lines)
                    changed = True

            #bloquea los inputs
            for widget in self.couple_data_list:
                self.w[widget].setEnabled(False)


            #el and verifica si paso el largo al torno
            if changed == True: #and self.iniciar_cliente(cuple_inputs_dict['largo_bruto']) #*****descomentar and
                if self.py_control_pins['CTRL_ch_od'].get() == False:
                    ACTION.OPEN_PROGRAM(self.program_not_od)
                else:
                    ACTION.OPEN_PROGRAM(self.program_od)
            
        except:
            changed = False
            self.add_status('No se puede reemplazar valores de cupla en programa principal del gantry.')
            print 'No se puede reemplazar valores de cupla en programa principal del gantry.'


    def touchoff(self, selector):
        return
        # if selector == 'touchplate':
        #     z_offset = float(self.w.lineEdit_touch_height.text())
        # elif selector == 'sensor':
        #     z_offset = float(self.w.lineEdit_sensor_height.text()) - float(self.w.lineEdit_work_height.text())
        # else:
        #     self.add_alarm("Unknown touchoff routine specified")
        #     return
        # self.add_status("Touchoff to {} started".format(selector))
        # max_probe = self.w.lineEdit_max_probe.text()
        # search_vel = self.w.lineEdit_search_vel.text()
        # probe_vel = self.w.lineEdit_probe_vel.text()
        # ACTION.CALL_MDI("G21 G49")
        # ACTION.CALL_MDI("G10 L20 P0 Z0")
        # ACTION.CALL_MDI("G91")
        # command = "G38.2 Z-{} F{}".format(max_probe, search_vel)
        # if ACTION.CALL_MDI_WAIT(command, 10) == -1:
        #     ACTION.CALL_MDI("G90")
        #     return
        # if ACTION.CALL_MDI_WAIT("G1 Z4.0"):
        #     ACTION.CALL_MDI("G90")
        #     return
        # ACTION.CALL_MDI("G4 P0.5")
        # command = "G38.2 Z-4.4 F{}".format(probe_vel)
        # if ACTION.CALL_MDI_WAIT(command, 10) == -1:
        #     ACTION.CALL_MDI("G90")
        #     return
        # command = "G10 L20 P0 Z{}".format(z_offset)
        # ACTION.CALL_MDI_WAIT(command)
        # command = "G1 Z10 F{}".format(search_vel)
        # ACTION.CALL_MDI_WAIT(command)
        # ACTION.CALL_MDI("G90")

    def kb_jog(self, state, joint, direction, fast = False, linear = True):
        if not STATUS.is_man_mode() or not STATUS.machine_is_on():
            self.add_status('Machine must be ON and in Manual mode to jog')
            return
        if linear:
            distance = STATUS.get_jog_increment()
            rate = STATUS.get_jograte()/60
        else:
            distance = STATUS.get_jog_increment_angular()
            rate = STATUS.get_jograte_angular()/60
        if state:
            if fast:
                rate = rate * 2
            ACTION.JOG(joint, direction, rate, distance)
        else:
            ACTION.JOG(joint, 0, 0, 0)

    def add_status(self, message):
        self._m = message
        print message
        self.w.statusbar.showMessage(self._m, 5000)
        STATUS.emit('update-machine-log', self._m, 'TIME')

    def enable_auto(self, state):
        for widget in self.auto_list:
            self.w[widget].setEnabled(state)
        if state is True:
            self.w.jogging_frame.show()
        else:
            self.w.jogging_frame.hide()
            self.w.main_tab_widget.setCurrentIndex(TAB_MAIN)
            self.w.stackedWidget.setCurrentIndex(0)
        self.w.stackedWidget_dro.setCurrentIndex(0)

    def enable_onoff(self, state):
        if state:
            self.add_status("Machine ON")
        else:
            self.add_status("Machine OFF")
        #self.w.spindle_pause.setChecked(False)
        self.h['eoffset_count'] = 0
        for widget in self.onoff_list:
            self.w[widget].setEnabled(state)

    def set_start_line(self, line):
        if line == 0:
            self.w.lbl_start_line.setText('1')
        # elif self.w.chk_run_from_line.isChecked():
        #     self.w.lbl_start_line.setText(str(line))
        else:
            self.w.lbl_start_line.setText('1')

    def use_keyboard(self):
        if self.w.chk_use_keyboard.isChecked():
            return True
        else:
            self.add_status('Keyboard shortcuts are disabled')
            return False

    def add_alarm(self, message):
        STATUS.emit('update-machine-log', message, 'TIME')


    #####################
    # KEY BINDING CALLS #
    #####################

    def on_keycall_ESTOP(self,event,state,shift,cntrl):
        if state:
            ACTION.SET_ESTOP_STATE(True)

    def on_keycall_POWER(self,event,state,shift,cntrl):
        if state:
            ACTION.SET_MACHINE_STATE(False)

    def on_keycall_ABORT(self,event,state,shift,cntrl):
        if state:
            ACTION.ABORT()

    def on_keycall_HOME(self,event,state,shift,cntrl):
        if state and not STATUS.is_all_homed() and self.use_keyboard():
            ACTION.SET_MACHINE_HOMING(-1)

    def on_keycall_pause(self,event,state,shift,cntrl):
        if state and STATUS.is_auto_mode() and self.use_keyboard():
            ACTION.PAUSE()

    def on_keycall_XPOS(self,event,state,shift,cntrl):
        if self.use_keyboard():
            self.kb_jog(state, 0, 1, shift)

    def on_keycall_XNEG(self,event,state,shift,cntrl):
        if self.use_keyboard():
            self.kb_jog(state, 0, -1, shift)

    def on_keycall_YPOS(self,event,state,shift,cntrl):
        if self.use_keyboard():
            self.kb_jog(state, 1, 1, shift)

    def on_keycall_YNEG(self,event,state,shift,cntrl):
        if self.use_keyboard():
            self.kb_jog(state, 1, -1, shift)

    def on_keycall_ZPOS(self,event,state,shift,cntrl):
        if self.use_keyboard():
            self.kb_jog(state, 2, 1, shift)

    def on_keycall_ZNEG(self,event,state,shift,cntrl):
        if self.use_keyboard():
            self.kb_jog(state, 2, -1, shift)
    
    def on_keycall_APOS(self,event,state,shift,cntrl):
        if self.use_keyboard():
            self.kb_jog(state, 3, 1, shift, False)

    def on_keycall_ANEG(self,event,state,shift,cntrl):
        if self.use_keyboard():
            self.kb_jog(state, 3, -1, shift, False)

    def on_keycall_F12(self,event,state,shift,cntrl):
        #print(dir(STYLEEDITOR))
        #argspec = inspect.getargspec(STYLEEDITOR.saveStyleSheet)
        #firma = inspect.formatargspec(*argspec)
        if state:
            STYLEEDITOR.load_dialog()

    ##############################
    # required class boiler code #
    ##############################
    def __getitem__(self, item):
        return getattr(self, item)

    def __setitem__(self, item, value):
        return setattr(self, item, value)

################################
# required handler boiler code #
################################



def get_handlers(halcomp, widgets, paths):
    return [HandlerClass(halcomp, widgets, paths)]

