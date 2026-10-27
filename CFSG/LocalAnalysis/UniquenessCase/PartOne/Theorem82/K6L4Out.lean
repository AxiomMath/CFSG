module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer centerQuotientOuterHom
  centerQuotient_outer_injective)

private theorem card_outer_dvd_eight {S : Type} [Group S] [Finite S] {r : ℕ} (hr : r.Prime)
    (h : (r ^ 1 % 3 = 1 ∧ LieModel S .PSL 4 r 1) ∨ (r ^ 1 % 3 = 2 ∧ LieModel S .PSU 4 r 1)) :
    Nat.card (Outer S) ∣ 2 ^ 3 := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨hdvd, -⟩ :=
      CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
        (Or.inl rfl) (by norm_num : 3 ≤ 4) hr le_rfl (h.statedClassicalModel (by decide))
    refine hdvd.trans ?_
    simp only [CFSG.RankThree.OuterOrder.determinantParameter]
    exact (mul_dvd_mul_left (2 * 1) (Nat.gcd_dvd_left 4 _)).trans (by norm_num)
  · obtain ⟨hdvd, -⟩ :=
      CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
        (Or.inr rfl) (by norm_num : 3 ≤ 4) hr le_rfl (h.statedClassicalModel (by decide))
    refine hdvd.trans ?_
    simp only [CFSG.RankThree.OuterOrder.determinantParameter]
    exact (mul_dvd_mul_left (2 * 1) (Nat.gcd_dvd_left 4 _)).trans (by norm_num)

theorem k6L4_out_two {Y : Type} [Group Y] [Finite Y] {r : ℕ} (hlie : IsLie811 Y .l4 r 1) :
    ∀ φ : MulAut Y, ∃ k : ℕ, φ ^ (2 ^ k) ∈ innAut Y := by
  obtain ⟨hq, -, hr, -, hm⟩ := hlie
  haveI : Group.IsPerfect Y := hq.1
  have hdvd := card_outer_dvd_eight hr hm
  intro φ
  refine ⟨3, ?_⟩
  have h1 : (centerQuotientOuterHom Y (QuotientGroup.mk φ)) ^ 2 ^ 3 = 1 := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, pow_card_eq_one', one_pow]
  have h2 : (QuotientGroup.mk φ : Outer Y) ^ 2 ^ 3 = 1 := by
    apply centerQuotient_outer_injective Y
    rw [map_pow, map_one]
    exact h1
  rw [← QuotientGroup.mk_pow] at h2
  exact (QuotientGroup.eq_one_iff
    (N := CFSG.ComponentClassification.OuterAutomorphisms.inner Y) _).1 h2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
