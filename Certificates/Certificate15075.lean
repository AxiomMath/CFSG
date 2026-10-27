module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8WInputs
import Certificates.Kernel.LocalComp.ExcO8W.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15075 : CFSG.ComponentClassification.RankTwoClassical.ExcO8W.censusArrCheck = true ∧
    CFSG.ComponentClassification.RankTwoClassical.ExcO8W.censusChainCheck = true ∧
    CFSG.ComponentClassification.RankTwoClassical.ExcO8W.censusCoverCheck = true ∧
    CFSG.ComponentClassification.RankTwoClassical.ExcO8W.censusFusionCheck = true ∧
    CFSG.ComponentClassification.RankTwoClassical.ExcO8W.censusDerivCheck = true := KernelLC.ExcO8W.facts

end Certificates
