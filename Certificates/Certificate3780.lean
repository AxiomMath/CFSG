module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelData
import Certificates.Kernel.OmegaEight.CPM

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.CPrimeModel in
theorem certificate3780 : (sigCheck .plus = true)
    ∧ (sigCheck .minus = true)
    ∧ (cosetCheck = true)
    ∧ (minusCheck = true) := KernelO8.cert3780

end Certificates
