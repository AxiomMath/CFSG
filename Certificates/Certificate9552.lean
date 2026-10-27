module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveData
import Certificates.Kernel.Sporadic.Fi22.Cent9552

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Fi22Five in
theorem certificate9552 : CFSG.AGLEmbedding.KFactProofs.Fi22Five.centCheck = true := KernelSpor.Fi22Cent8.c9552

end Certificates
