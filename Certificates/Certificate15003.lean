module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ3W
import Certificates.Kernel.Census.J3.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.J3 CFSG.KC.Census in
theorem certificate15003 : ∃ (si xe : Array ℕ) (ws : List (List ℕ)) (d : ConjDataP), j3CheckW si xe ws d = true := KernelCensus.J3.j3_ok

end Certificates
