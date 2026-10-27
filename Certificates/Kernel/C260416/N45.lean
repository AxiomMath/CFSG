module

public import Certificates.Data.Kernel.B45HM22.Nor
public import Certificates.Data.SmithB45HM22Nor

public section

namespace CFSG.KD.C260416

open CFSG.KC.B45HM22 CFSG.Quasithin.HM22

theorem chk45 : norP 45 nor45 std45A std45B = true := by
  decide +kernel

end CFSG.KD.C260416

end
