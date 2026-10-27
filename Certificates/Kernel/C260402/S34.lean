module

public import Certificates.Data.SmithB45MatM22Mod
public import Certificates.Kernel.C260402.Pins
public import Certificates.Data.Kernel.B45M12.Mask

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M22

theorem sub34 : subK 100 34 (trM 34 B34Rows) (trM 100 P34Rows)
    [(kronM 10 10 C10bA C10bA, T34A), (kronM 10 10 C10bB C10bB, T34B),
      (kronM 10 10 C10bG11 C10bG11, T34G11)] = true := by
  decide +kernel

end CFSG.KD.C260402

end
