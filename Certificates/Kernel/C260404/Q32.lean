module

public import Certificates.Data.Kernel.B45M12.Mask
public import Certificates.Data.SmithB45MatM12Mod
public import Certificates.Kernel.C260404.Pins

public section

namespace CFSG.KD.C260404

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12

theorem quot32 : quotK 230 32 Bsel Psel [(T230A, T32A), (T230B, T32B)] = true := by
  decide +kernel

end CFSG.KD.C260404

end
