module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutData
import Certificates.Kernel.HS100.S5OGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HSStd in
theorem certificate26961 : s5oOK = true := KernelHS100.s5o

end Certificates
