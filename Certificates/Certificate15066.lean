module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6TwoTests
import Certificates.Kernel.LocalComp.TwistedE6Two

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15066 : CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two.factorCheck = true ∧
    CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two.conjCheck = true := KernelLC.TwistedE6Two.cert15066

end Certificates
