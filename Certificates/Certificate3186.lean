module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylTData
import Certificates.Kernel.LocalComp.Weyl3186

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem certificate3186 : TListFacts
    ∧ (rhoWordCheck = true)
    ∧ (tGenCheck = true) := KernelLC.W3186.cert3186

end Certificates
