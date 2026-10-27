module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1AutData
import Certificates.Kernel.OmegaEight.Aut

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model in
theorem certificate3373 : (autCheck .plus = true)
    ∧ (autCheck .minus = true) := KernelO8.cert3373

end Certificates
