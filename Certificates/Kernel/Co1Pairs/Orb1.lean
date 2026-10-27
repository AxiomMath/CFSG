module

public import Certificates.Data.Kernel.F2Set24
public import Certificates.Kernel.Co1Pairs.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo1Pairs

open CFSG.KC.F2Set24 CFSG.KD.Co1Pairs

theorem ch214033o1 : orbOK c2 c3 o2 o3 1059 1701 13 = true := by quickRfl

end CertificateChecks.KernelCo1Pairs

end
