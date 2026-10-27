module

public import Certificates.Data.Kernel.B3SixD
public import Certificates.Data.Kernel.B3SixLit

public section

set_option Elab.async false
set_option maxRecDepth 100000

namespace CFSG.KD.B3SixDGUT0

open CFSG.Quasithin.B3 CFSG.KC.B3Six

theorem eq_ok : eqD (fourDX sym6K Mod.ut0 true) dGT0D = true := by decide +kernel

theorem struct_ok : chkStruct6D sym6K dGT0D Mod.ut0 true 4 = true := by decide +kernel

theorem gen_ok : chkGenG6D dGT0D = true := by decide +kernel

theorem sub_ok : chkSubG6D sym6K wG6 dGT0D Mod.ut0 = true := by decide +kernel

theorem wit_ok : chkWitG6D sym6K dGT0D Mod.ut0 = true := by decide +kernel

theorem rg_ok : chkRG6D dGT0D = true := by decide +kernel

end CFSG.KD.B3SixDGUT0

end
