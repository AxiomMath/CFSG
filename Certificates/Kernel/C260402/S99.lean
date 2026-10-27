module

public import Certificates.Data.SmithB45MatM22Mod
public import Certificates.Kernel.C260402.Pins
public import Certificates.Data.Kernel.B45M12.Mask

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M22

theorem sub99 : subK 100 99 (trM 99 B99Rows) (trM 100 P99Rows)
    [(kronM 10 10 C10aA C10bA, T99A), (kronM 10 10 C10aB C10bB, T99B)] = true := by
  decide +kernel

end CFSG.KD.C260402

end
