module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1CohSpans
import Certificates.Kernel.OmegaEight.CohCert

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Stage1 in
theorem certificate3371 : (relCheck6 .plus = true)
    ∧ (relCheck6 .minus = true)
    ∧ gamSpans .plus
    ∧ gamSpans .minus
    ∧ extSpans .plus
    ∧ extSpans .minus := KernelO8.CohCert.cert3371

end Certificates
