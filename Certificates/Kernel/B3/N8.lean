module

public import Certificates.Kernel.B3.D8

public section

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 200

namespace CFSG.KD.B3M8

open CFSG.KC.B3M

theorem tm_ok : chkTM dat = true := by decide +kernel

theorem ea_ok : chkEAM dat = true := by decide +kernel

theorem named_ok : chkNamedM dat = true := by decide +kernel

theorem mod0_ok : chkModM dat 0 = true := by decide +kernel

theorem mod1_ok : chkModM dat 1 = true := by decide +kernel

theorem mod2_ok : chkModM dat 2 = true := by decide +kernel

theorem mod3_ok : chkModM dat 3 = true := by decide +kernel

end CFSG.KD.B3M8

end
