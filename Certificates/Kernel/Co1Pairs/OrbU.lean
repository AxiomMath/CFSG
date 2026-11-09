module

public import Certificates.Data.Kernel.F2Orb24
public import Certificates.Kernel.Co1Pairs.Data
public import Certificates.Kernel.Co1Pairs.SparseData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 1000000

namespace CertificateChecks.KernelCo1Pairs

open CFSG.KC.F2Orb24 CFSG.KD.Co1Pairs

theorem ch36909s : sparseK c8 c9 1 1920 sU = true := by quickRfl

end CertificateChecks.KernelCo1Pairs

end
