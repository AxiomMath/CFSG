module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H21
public import CFSG.RankThree.SteinbergR3EHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Quasithin CFSG.ComponentClassification.OuterAutomorphisms

theorem card_mulAut_dvd_of_outer {Y : Type} [Group Y] [Finite Y] {c : ℕ}
    (h : Nat.card (Outer Y) ∣ c) : Nat.card (MulAut Y) ∣ c * Nat.card Y := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner Y)
  have h2 : Nat.card (inner Y) ∣ Nat.card Y := by
    have := card_eq_ker_mul_range (MulAut.conj : Y →* MulAut Y)
    exact ⟨_, this.trans (mul_comm _ _)⟩
  rw [h1]
  exact Nat.mul_dvd_mul h h2

theorem card_mulAut_dvd_of_psl34 {Y : Type} [Group Y] [Finite Y] (h : IsPSL 3 2 2 Y) :
    Nat.card (MulAut Y) ∣ 12 * Nat.card Y := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hO := CFSG.RankThree.Automorphisms.higher_linear_outer_order_divides_field_scalar_bound
    (K := K) Nat.prime_two (by norm_num : 1 ≤ 2) (le_refl 3) hK
  let e' : Y ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 K))
  refine card_mulAut_dvd_of_outer ?_
  rw [Nat.card_congr (equivalence e').toEquiv]
  simpa using hO

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
