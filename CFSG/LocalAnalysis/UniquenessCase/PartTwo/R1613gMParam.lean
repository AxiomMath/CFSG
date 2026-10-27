module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem r1613g_mParam_ne_zero {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} (hA : A ≠ ⊥) : E3.mParam A ≠ 0 := by
  by_cases hev : Even (Nat.card ↥A)
  · unfold E3.mParam
    rw [if_pos hev]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 2 (even_iff_two_dvd.1 hev)
    set S : Set ℕ :=
      {n : ℕ | ∃ t ∈ A, orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))} with hS
    have hne : S.Nonempty :=
      ⟨_, (x : MulAut W), x.2, by rw [Subgroup.orderOf_coe]; exact hx, rfl⟩
    obtain ⟨t, -, ht2, hteq⟩ := Nat.sInf_mem hne
    intro h0
    rw [hteq, rkIdx_fixV_zpowers, commV_eq_commSub, rk_eq_zero_iff hW, commSub_eq_bot_iff] at h0
    have ht1 : t = 1 := by
      refine MulEquiv.ext fun w => ?_
      exact h0 (Subgroup.mem_top w) t (Subgroup.mem_zpowers t)
    rw [ht1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  · unfold E3.mParam
    rw [if_neg hev]
    intro h0
    have hcard : Nat.card W = 1 := by
      rw [card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW), h0, pow_zero]
    haveI : Subsingleton W := (Nat.card_eq_one_iff_unique.1 hcard).1
    apply hA
    rw [Subgroup.eq_bot_iff_forall]
    intro t _
    exact MulEquiv.ext fun w => Subsingleton.elim _ _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
