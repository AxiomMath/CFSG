module

public import Certificates.Data.Kernel.B45M12.Mask
public import Certificates.Data.SmithB45MatM12Mod
public import Certificates.Kernel.C260404.Pins

public section

namespace CFSG.KD.C260404

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12

theorem sub144A : subK 440 144 B144 P144 [(kronM 10 44 (cols10 arrA) T44A, T144A)] = true := by
  decide +kernel

end CFSG.KD.C260404

end
