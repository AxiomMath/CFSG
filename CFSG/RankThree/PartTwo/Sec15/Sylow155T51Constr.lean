module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ConstrainedQuotient
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs245b

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155T51

variable {M : Type} [Group M] [Finite M]

theorem not_isPConstrained_quotient (h : ¬ CFSG.ABGLocalTools.IsPConstrained 3 M) :
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 (M ⧸ CFSG.pPrimeCore 3 M) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hq
  apply h
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.isPConstrained_iff_hasPrimeConstraint] at hq ⊢
  refine CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.hasPrimeConstraint_of_surjective_of_coprime_ker_rev
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 M)) (QuotientGroup.mk'_surjective _) ?_ hq
  rw [QuotientGroup.ker_mk']
  exact CFSG.pPrimeCore_coprime_card

theorem exists_isComponent_of_not_isPConstrained
    (h : ¬ CFSG.ABGLocalTools.IsPConstrained 3 M) :
    ∃ Y : Subgroup (M ⧸ CFSG.pPrimeCore 3 M), CFSG.IsComponent Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245b.exists_component_of_not_isPConstrained
      Nat.prime_three (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3)
      (not_isPConstrained_quotient h)
  exact ⟨K, (CFSG.isComponent_iff_open K).mpr hK⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155T51
