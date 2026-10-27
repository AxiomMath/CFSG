module

public import Certificates.Data.Kernel.B45M12.Mask
public import Certificates.Data.SmithB45MatM12Mod
public import Certificates.Kernel.C260404.Pins

public section

namespace CFSG.KD.C260404

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12

theorem sub230A : subK 440 230 B230 P230 [(kronM 10 44 (cols10 arrA) T44A, T230A)] = true := by
  decide +kernel

end CFSG.KD.C260404

end
