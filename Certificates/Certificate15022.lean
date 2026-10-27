module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuR
import Certificates.Kernel.Census.RuR.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Ru CFSG.KC.Census in
theorem certificate15022 : ∃ (d : ConjDataP) (ps : List ℕ) (e0 : Array ℕ) (L : ℕ → ℕ) (pe : Array ℕ) (O ix : ℕ)
      (xw : List (List ℕ)) (wits : List (ℕ × ℕ × List (ℕ × List ℕ × List ℕ) × ℕ))
      (em yw : List ℕ),
    ruCheckR d ps e0 L pe O ix xw wits em yw = true := KernelCensus.RuR.ru_census

end Certificates
