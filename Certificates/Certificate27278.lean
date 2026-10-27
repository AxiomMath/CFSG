module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCases
import Certificates.Kernel.HSStd.U43VaGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HSStd.U43 in
theorem certificate27278 : vaCheck = true := KernelHSStd.U43Va.vaCheck_true

end Certificates
