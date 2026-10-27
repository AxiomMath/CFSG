module

public import Certificates.Data.Kernel.B45M12.Mask
public import Certificates.Data.SmithB45MatM12Mod
public import Certificates.Kernel.C260404.Pins

public section

namespace CFSG.KD.C260404

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12

theorem sub44 : subK 100 44 B44 P44 [(K100 arrA, T44A), (K100 arrB, T44B)] = true := by
  decide +kernel

theorem bound44 : P44.all (· < 2 ^ 44) = true := by
  decide +kernel

end CFSG.KD.C260404

end
