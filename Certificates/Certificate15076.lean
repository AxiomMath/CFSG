module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8EInputs
import Certificates.Kernel.LocalComp.ExcO8E.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15076 : CFSG.ComponentClassification.RankTwoClassical.ExcO8E.censusArrCheck = true ∧
    CFSG.ComponentClassification.RankTwoClassical.ExcO8E.censusChainCheck = true ∧
    CFSG.ComponentClassification.RankTwoClassical.ExcO8E.censusCoverCheck = true ∧
    CFSG.ComponentClassification.RankTwoClassical.ExcO8E.censusFusionCheck = true ∧
    CFSG.ComponentClassification.RankTwoClassical.ExcO8E.censusDerivCheck = true := KernelLC.ExcO8E.facts

end Certificates
