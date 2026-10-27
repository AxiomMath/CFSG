module

public import Certificates.Kernel.Co1P.Defs21154
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Co1PText

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KLie.CT CFSG.Sporadic.Co1Patterson.Native

theorem q2_small0 : q2SmallK 0 = true := by quickRfl

theorem q2_small1 : q2SmallK 1 = true := by quickRfl

theorem q2_small2 : q2SmallK 2 = true := by quickRfl

theorem q2_small3 : q2SmallK 3 = true := by quickRfl

end CertificateChecks.KernelCo1P

end
