module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelWit
import Certificates.Kernel.OmegaEight.ModelCert

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model in
theorem certificate3372 : (chainCheck .plus = true)
    ∧ (chainCheck .minus = true)
    ∧ (basicCheck .plus = true)
    ∧ (basicCheck .minus = true)
    ∧ (∃ T, oSetCheckW .plus T = true ∧ r3CheckW T = true)
    ∧ (∃ T, oSetCheckW .minus T = true)
    ∧ (∃ S D, s5CheckW .plus S D = true)
    ∧ (∃ S D, s5CheckW .minus S D = true) := KernelO8.cert3372

end Certificates
