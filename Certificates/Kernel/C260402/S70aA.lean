module

public import Certificates.Data.Kernel.B45M22.Defs
public import Certificates.Data.SmithB45MatM22Mod
public import Certificates.Kernel.C260402.Pins

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M12 CFSG.KC.B45M22 CFSG.Quasithin.B45Mat.M22

theorem sub70aA : subF4K 340 70 (colsD 70 7 B70aRows) (ofF2 P70aC)
    [(k340 C10bA T34A, T70aA)] = true := by
  decide +kernel

end CFSG.KD.C260402

end
