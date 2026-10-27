module

public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c15t_transvection_of_rk_commSub_le_one (hW : ∀ w : W, w ^ 2 = 1) {U : Subgroup W}
    {e : MulAut W} (h : rk ↥(commSub U (Subgroup.zpowers e)) ≤ 1) :
    (∀ x ∈ U, e x = x) ∨ ∃ c : W, c ≠ 1 ∧ ∀ x ∈ U, e x = x ∨ e x = x * c := by
  set C := commSub U (Subgroup.zpowers e) with hC
  have hmem : ∀ x ∈ U, e x * x⁻¹ ∈ C := fun x hx =>
    Subgroup.subset_closure ⟨e, Subgroup.mem_zpowers e, x, hx, rfl⟩
  have hcard : Nat.card C = 2 ^ rk ↥C := card_eq_two_pow hW C
  by_cases h0 : rk ↥C = 0
  · left
    have hbot : C = ⊥ := (rk_eq_zero_iff hW).1 h0
    intro x hx
    have h1 := hmem x hx
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  · right
    have h1 : rk ↥C = 1 := by omega
    have hc2 : Nat.card C = 2 := by rw [hcard, h1]; norm_num
    obtain ⟨c, hc1, huniq⟩ := (Nat.card_eq_two_iff' (1 : C)).1 hc2
    refine ⟨(c : W), fun h1' => hc1 (Subtype.ext h1'), fun x hx => ?_⟩
    by_cases hz : (⟨e x * x⁻¹, hmem x hx⟩ : C) = 1
    · left
      have : e x * x⁻¹ = 1 := congrArg Subtype.val hz
      exact mul_inv_eq_one.1 this
    · right
      have hzc := huniq _ hz
      have : e x * x⁻¹ = (c : W) := congrArg Subtype.val hzc
      calc e x = (e x * x⁻¹) * x := by group
        _ = (c : W) * x := by rw [this]
        _ = x * c := mul_comm _ _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
