module

public import Certificates.Data.Kernel.F2Set24
public import Certificates.Kernel.Co1Pairs.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo1Pairs

open CFSG.KC.F2Set24 CFSG.KD.Co1Pairs

theorem ch214033o2 : orbOK c4 c5 o4 o5 18 3240 15 = true := by quickRfl

end CertificateChecks.KernelCo1Pairs

end
