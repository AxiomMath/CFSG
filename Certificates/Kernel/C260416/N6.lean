module

public import Certificates.Data.Kernel.B45HM22.Nor
public import Certificates.Data.SmithB45HM22Nor

public section

namespace CFSG.KD.C260416

open CFSG.KC.B45HM22 CFSG.Quasithin.HM22

theorem chk6 : norP 6 nor6 n1P n2P = true := by
  decide +kernel

theorem chk15 : norP 15 nor15 std15A std15B = true := by
  decide +kernel

end CFSG.KD.C260416

end
