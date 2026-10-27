module

public import Certificates.Kernel.Co1P.Defs21152
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KLie.CT

theorem lvl2_ok : allN 7 lvl2K = true := by quickRfl

theorem far_ok : allN 2 farK = true := by quickRfl

theorem ae_ok : aeK = true := by quickRfl

end CertificateChecks.KernelCo1P

end
