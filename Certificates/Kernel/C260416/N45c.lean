module

public import Certificates.Data.Kernel.B45HM22.Nor
public import Certificates.Data.SmithB45HM22Nor

public section

namespace CFSG.KD.C260416

open CFSG.KC.B45HM22 CFSG.Quasithin.HM22

theorem chk45c : norP 45 nor45c std45cA std45cB = true := by
  decide +kernel

end CFSG.KD.C260416

end
