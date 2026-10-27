module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagGriess
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow

public section

open CFSG Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

section Certified


theorem fa_ON {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (hZ3 : IsPGroup 3 (Subgroup.center J)) (hZ : Subgroup.center J ≠ ⊥)
    (e : J ⧸ Subgroup.center J ≃* CFSG.Blueprint.NativeSporadic.ON) (S : Sylow 3 J) :
    ∃ x ∈ (S : Subgroup J), ∃ y ∈ (S : Subgroup J), x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  have hdvd : Nat.card (Subgroup.center J) ∣ 3 :=
    CFSG.RankThree.PartTwo.Sec4.diag_coverCenterThree_holds J hq hZ3
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩))))))
  have hcard3 : Nat.card (Subgroup.center J) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hZ
    · exact h3
  have e' : J ⧸ Subgroup.center J ≃* CFSG.Blueprint.NativeSporadic.Carrier .ONan := e
  obtain ⟨π, hπ, hker⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_surj_ker_center
      (MulEquiv.refl (CFSG.Blueprint.NativeSporadic.Carrier .ONan)) e'
  have hD : CFSG.AGLEmbedding.AbelianSylowDatum (CFSG.Blueprint.NativeSporadic.Carrier .ONan) 3 :=
    CFSG.AGLEmbedding.abelianSylowDatum_ON_three
  have hcardY : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .ONan) = 460815505920 :=
    CFSG.Sporadic.ON.card_ON
  obtain ⟨hcard, hexp, -, hcen⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.sylow_hat_on hD hcardY hq.1.commutator_eq_top hcard3
      π hπ hker S
  have hnc : ¬ ∀ x ∈ (S : Subgroup J), ∀ y ∈ (S : Subgroup J), x * y = y * x := by
    intro h
    have hle : (S : Subgroup J) ≤ Subgroup.center J :=
      fun x hx => hcen x hx (fun g hg => h g hg x hx)
    have hle' := Subgroup.card_le_of_le hle
    rw [hcard, hcard3] at hle'
    norm_num at hle'
  push Not at hnc
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  exact ⟨x, hx, y, hy, hexp x hx, hexp y hy, hxy⟩

end Certified

end CFSG.RankThree.PartTwo.Sec11
