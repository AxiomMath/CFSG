module

public import Certificates.Data.SmithB45MatM22Mod
public import Certificates.Kernel.C260402.Pins
public import Certificates.Data.Kernel.B45M12.Mask

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M22

theorem quot98 : quotK 99 98 (trM 98 B98Rows) (trM 99 P98Rows)
    [(T99A, T98A), (T99B, T98B)] = true := by
  decide +kernel

end CFSG.KD.C260402

end
