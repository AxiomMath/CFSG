module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2R
import Certificates.Kernel.Census.Co2R.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Co2 CFSG.KC.Census in
theorem certificate15009 : ∃ (L : ℕ → ℕ) (pxs : List ℕ) (rs : List RootR), co2CheckR L pxs rs = true := KernelCensus.Co2R.co2_census

end Certificates
