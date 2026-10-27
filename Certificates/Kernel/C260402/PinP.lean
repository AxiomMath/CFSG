module

public import Certificates.Data.Kernel.B45M22.Defs
public import Certificates.Data.SmithB45MatM22Mod
public import Certificates.Kernel.C260402.Pins

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M12 CFSG.KC.B45M22 CFSG.Quasithin.B45Mat.M22

theorem pinP70a : eqF4 340 (trF4 70 (ofF2 P70aC)) (P70aRows.map (deint 9)) = true := by
  decide +kernel

end CFSG.KD.C260402

end
