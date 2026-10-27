module

public import Certificates.Data.Kernel.B45M22.Defs
public import Certificates.Data.SmithB45MatM22Mod
public import Certificates.Kernel.C260402.Pins

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M12 CFSG.KC.B45M22 CFSG.Quasithin.B45Mat.M22

theorem trace70a : traceK 70
    (mulF4 (ofF2 P70aC) (mulF4 (k340 C10bG11 T34G11) (colsD 70 7 B70aRows))) 2 = true := by
  decide +kernel

end CFSG.KD.C260402

end
