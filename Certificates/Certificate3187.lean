module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCoordData
import Certificates.Kernel.LocalComp.Weyl3187

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem certificate3187 : (coordCheck = true) := KernelLC.W3187.cert3187

end Certificates
