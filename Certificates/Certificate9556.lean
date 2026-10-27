module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
import Certificates.Kernel.Sporadic.Fi22.FiveK

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Fi22Five in
theorem certificate9556 : genCheck = true := KernelSpor.Fi22FiveK.gen

end Certificates
