module

public import Certificates.Data.Kernel.F2Set24
public import Certificates.Kernel.Co1Pairs.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo1Pairs

open CFSG.KC.F2Set24 CFSG.KD.Co1Pairs

theorem ch36909o : orbOK c8 c9 o8 o9 1 1920 15 = true := by quickRfl

end CertificateChecks.KernelCo1Pairs

end
