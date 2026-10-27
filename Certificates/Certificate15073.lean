module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcSp6Inputs
import Certificates.Kernel.LocalComp.ExcSp6.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15073 : CFSG.ComponentClassification.RankTwoClassical.ExcSp6.censusArrCheck = true ∧
    CFSG.ComponentClassification.RankTwoClassical.ExcSp6.censusChainCheck = true ∧
    CFSG.ComponentClassification.RankTwoClassical.ExcSp6.censusCoverCheck = true ∧
    CFSG.ComponentClassification.RankTwoClassical.ExcSp6.censusFusionCheck = true ∧
    CFSG.ComponentClassification.RankTwoClassical.ExcSp6.censusDerivCheck = true := KernelLC.ExcSp6.facts

end Certificates
