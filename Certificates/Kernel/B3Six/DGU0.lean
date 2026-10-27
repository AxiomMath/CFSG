module

public import Certificates.Data.Kernel.B3SixD
public import Certificates.Data.Kernel.B3SixLit

public section

set_option Elab.async false
set_option maxRecDepth 100000

namespace CFSG.KD.B3SixDGU0

open CFSG.Quasithin.B3 CFSG.KC.B3Six

theorem eq_ok : eqD (fourDX sym6K Mod.u0 true) dG0D = true := by decide +kernel

theorem struct_ok : chkStruct6D sym6K dG0D Mod.u0 true 4 = true := by decide +kernel

theorem gen_ok : chkGenG6D dG0D = true := by decide +kernel

theorem sub_ok : chkSubG6D sym6K wG6 dG0D Mod.u0 = true := by decide +kernel

theorem wit_ok : chkWitG6D sym6K dG0D Mod.u0 = true := by decide +kernel

theorem rg_ok : chkRG6D dG0D = true := by decide +kernel

end CFSG.KD.B3SixDGU0

end
