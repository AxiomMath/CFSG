module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83PairE6Tests
import Certificates.Kernel.LocalComp.PairE6

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15074 : CFSG.ComponentClassification.RankTwoExceptional.PairE6.pairCheckU = true ∧
    CFSG.ComponentClassification.RankTwoExceptional.PairE6.pairCheckV = true := KernelLC.PairE6.cert15074

end Certificates
