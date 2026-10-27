module

public import Certificates.Kernel.Co1P.Defs21150Q
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Co1PText
public import Certificates.Kernel.Co1P.Defs21150
public import Certificates.Kernel.Co1P.Defs21150S
public import Certificates.Kernel.Co1P.Defs21151

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK CFSG.Sporadic.Co1Patterson.Native

theorem q_ok : andB qClosT (distinctK 10 (modL QL)) = true := by quickRfl

end CertificateChecks.KernelCo1P

end
