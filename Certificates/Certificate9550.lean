module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveData
import Certificates.Kernel.Sporadic.Fi22.FiveK

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Fi22Five in
theorem certificate9550 : orbCheck = true := KernelSpor.Fi22FiveK.orb

end Certificates
