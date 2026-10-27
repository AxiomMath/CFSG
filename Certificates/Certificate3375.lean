module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelWit
import Certificates.Kernel.OmegaEight.ModelCert

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model in
theorem certificate3375 : ∃ F, q3CheckW F = true := KernelO8.cert3375

end Certificates
