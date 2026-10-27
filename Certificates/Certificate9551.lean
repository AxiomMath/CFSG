module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveData
import Certificates.Kernel.Sporadic.Fi22.B9551Final

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Fi22Five in
theorem certificate9551 : boundCheck = true := KernelSpor.B9551.bound

end Certificates
