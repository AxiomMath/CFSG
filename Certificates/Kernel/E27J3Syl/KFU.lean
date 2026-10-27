module

public import Certificates.Kernel.E27J3Syl.KU
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.E27J3Syl.K
public import Certificates.Kernel.E27J3Syl.KF

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kc_each CFSG.KD.E27J3S.c131001Hu 0 16

namespace CFSG.KD.E27J3S

theorem c131001_hsv : c131001Hsv = true := by
  quickRfl

end CFSG.KD.E27J3S

#kc_each CFSG.KD.E27J3S.c131001Fp 0 4

end
