module

public import Certificates.Data.Kernel.F2Orb24
public import Certificates.Kernel.Co1Pairs.Data
public import Certificates.Kernel.Co1Pairs.SparseData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 1000000

namespace CertificateChecks.KernelCo1Pairs

open CFSG.KC.F2Orb24 CFSG.KD.Co1Pairs

theorem ch214033s1 : sparseK c2 c3 1059 1701 s1 = true := by quickRfl

end CertificateChecks.KernelCo1Pairs

end
