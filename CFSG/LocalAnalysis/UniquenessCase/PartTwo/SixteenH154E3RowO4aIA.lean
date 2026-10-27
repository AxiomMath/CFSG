module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem s16h_H5_l2_four_outer_card_dvd_four {X : Type} [Group X]
    (hX : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 X (2 * 2)) :
    Nat.card (Outer X) ∣ 4 := by
  have hm : CFSG.Open.StatedClassicalModel X .PSL 2 2 (2 * 2) :=
    hX.statedClassicalModel (by decide)
  obtain ⟨⟨-, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  let e' : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hdvd : Nat.card (Outer X) ∣ (2 * 2) * Nat.gcd 2 (2 ^ (2 * 2) - 1) :=
    (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor Nat.prime_two K hK).2 X
      ⟨e'⟩
  convert hdvd using 1

theorem s16h_H5_isInner_of_pow_three {X : Type} [Group X]
    (hO : Nat.card (Outer X) ∣ 4) {α : MulAut X} (hα : α ^ 3 = 1) : α ∈ inner X := by
  set o : Outer X := QuotientGroup.mk α with ho
  have ho3 : o ^ 3 = 1 := by rw [ho, ← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have h1 : orderOf o ∣ Nat.gcd 3 4 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ho3) ((orderOf_dvd_natCard o).trans hO)
  have h2 : orderOf o = 1 := Nat.dvd_one.mp (by simpa using h1)
  rw [orderOf_eq_one_iff, ho, QuotientGroup.eq_one_iff] at h2
  exact h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
