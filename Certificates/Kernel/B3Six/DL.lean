module

public import Certificates.Data.Kernel.B3SixD
public import Certificates.Data.Kernel.B3SixLit

public section

set_option Elab.async false
set_option maxRecDepth 100000

namespace CFSG.KD.B3SixDL

open CFSG.Quasithin.B3 CFSG.KC.B3Six

theorem eq_u0 : eqD (fourDX sym6K Mod.u0 false) dL0D = true := by decide +kernel

theorem struct_u0 : chkStruct6D sym6K dL0D Mod.u0 false 3 = true := by decide +kernel

theorem sub_u0 : chkSubL6D sym6K dL0D Mod.u0 = true := by decide +kernel

theorem r_u0 : chkRL6D dL0D Mod.u0 = true := by decide +kernel

theorem eq_ut0 : eqD (fourDX sym6K Mod.ut0 false) dLT0D = true := by decide +kernel

theorem struct_ut0 : chkStruct6D sym6K dLT0D Mod.ut0 false 3 = true := by decide +kernel

theorem sub_ut0 : chkSubL6D sym6K dLT0D Mod.ut0 = true := by decide +kernel

theorem r_ut0 : chkRL6D dLT0D Mod.ut0 = true := by decide +kernel

end CFSG.KD.B3SixDL

end
