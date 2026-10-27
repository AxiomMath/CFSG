module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcU6Inputs
import Certificates.Kernel.LocalComp.ExcU6.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15070 : 
    CFSG.ComponentClassification.RankTwoClassical.ExcU6.censusChainCheck = true ∧
      CFSG.ComponentClassification.RankTwoClassical.ExcU6.censusCoverCheck = true ∧
      CFSG.ComponentClassification.RankTwoClassical.ExcU6.censusSizeCheck = true ∧
      CFSG.ComponentClassification.RankTwoClassical.ExcU6.censusPointCheck = true ∧
      CFSG.ComponentClassification.RankTwoClassical.ExcU6.censusDerivCheck = true := KernelLC.ExcU6.facts

end Certificates
