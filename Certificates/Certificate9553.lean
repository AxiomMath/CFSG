module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
import Certificates.Kernel.Sporadic.Fi22.Cent9553

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Fi22Five in
theorem certificate9553 : star5Check = true := KernelSpor.Fi22Cent.c9553

end Certificates
