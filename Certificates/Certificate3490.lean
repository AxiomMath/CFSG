module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainModSpans
import Certificates.Kernel.OmegaEight.CohCert

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Chain CFSG.EvenSmallLie.OmegaEight.Stage1 in
theorem certificate3490 : endSpans .plus
    ∧ endSpans .minus
    ∧ modSpans .plus
    ∧ modSpans .minus := KernelO8.CohCert.cert3490

end Certificates
