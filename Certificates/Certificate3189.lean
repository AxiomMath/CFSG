module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylD8Data
import Certificates.Kernel.LocalComp.Weyl3189

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem certificate3189 : dCheck = true := KernelLC.W3189.cert3189

end Certificates
