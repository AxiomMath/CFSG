module

public import Certificates.Kernel.Co3T.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co3T.EnumQ

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3T

open CFSG.KC.Enum CFSG.KC.Co3TK

theorem kHyp : allN 121 hypK = true := by quickRfl

theorem kFus : allN 2187 (fusK TT.L DE EQ.T FW FA FB) = true := by quickRfl

end CertificateChecks.KernelCo3T

end
