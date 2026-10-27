module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverKInputs
import Certificates.Kernel.Sporadic.OddCore.U43CoverKF

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HSStd.U43 in
theorem certificate27272 : kCheck = true := KernelSpor.U43CoverK.facts27272

end Certificates
