module

public import Certificates.Data.Kernel.B45HM22.Nor
public import Certificates.Data.SmithB45HM22Nor

public section

namespace CFSG.KD.C260416

open CFSG.KC.B45HM22 CFSG.Quasithin.HM22

theorem chk84 : norP 84 nor84 std84A std84B = true := by
  decide +kernel

end CFSG.KD.C260416

end
