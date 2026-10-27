module

public import Certificates.Kernel.Co2JRank.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2JRank

open CFSG.KC.Co2InvS CFSG.KC.Co2JRank

theorem wWalk : walkJ WG (pt1 CRW K1W) 5 IDP 0 = true := by quickRfl

theorem wNz : nzK K1W 32 1 = true := by quickRfl

theorem wPar : parK K1W 5 = true := by quickRfl

end CertificateChecks.KernelSpor.Co2JRank

end
