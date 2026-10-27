module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatInvol.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

variable {V : Type} [CommGroup V]

theorem eq_one_of_commute_of_isIrrOn (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    (hirr : IsIrrOn H ⊤ ⊥) {t : MulAut V} (ht : t ^ 2 = 1)
    (hcomm : ∀ h ∈ H, t * h = h * t) : t = 1 := by
  set C : Subgroup V := commSub ⊤ (Subgroup.zpowers t) with hC
  have hgen : ∀ w : V, t (t w * w⁻¹) = t w * w⁻¹ := by
    intro w
    have htt : t (t w) = w := by
      have := congrArg (fun f : MulAut V => f w) ht
      simpa [sq, MulAut.mul_apply] using this
    rw [map_mul, map_inv, htt]
    have h2 : (t w) ^ 2 = 1 := hV _
    have h3 : w ^ 2 = 1 := hV _
    rw [sq] at h2 h3
    calc w * (t w)⁻¹ = (t w)⁻¹ * w := mul_comm _ _
      _ = t w * w⁻¹ := by rw [inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3]
  have hCfix : C ≤ fixV (Subgroup.zpowers t) := by
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨x, hx, w, -, rfl⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [SetLike.mem_coe, mem_fixV]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hpow : ∀ z : ℤ, t ^ z = 1 ∨ t ^ z = t := by
      intro z
      have h2 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one ht
      rcases Int.even_or_odd z with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · left
        rw [← two_mul, zpow_mul, show (t ^ (2 : ℤ)) = 1 by exact_mod_cast ht, one_zpow]
      · right
        rw [zpow_add, zpow_mul, show (t ^ (2 : ℤ)) = 1 by exact_mod_cast ht, one_zpow, one_mul,
          zpow_one]
    rcases hpow m with hm | hm <;> rcases hpow j with hj | hj <;> rw [hm, hj] <;>
      simp [hgen]
  have hCst : StableUnder H C := by
    intro h hh c hc
    refine Subgroup.closure_induction (p := fun c _ => h c ∈ C) ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨x, hx, w, -, rfl⟩
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hcm : h * t ^ m = t ^ m * h := by
        have := (Commute.zpow_left (show Commute t h from hcomm h hh) m)
        exact this.eq.symm
      refine Subgroup.subset_closure ⟨t ^ m, Subgroup.zpow_mem_zpowers t m, h w,
        Subgroup.mem_top _, ?_⟩
      rw [map_mul, map_inv]
      have := congrArg (fun f : MulAut V => f w) hcm
      simp only [MulAut.mul_apply] at this
      rw [this]
    · rw [map_one]
      exact C.one_mem
    · intro x y _ _ hx hy
      rw [map_mul]
      exact C.mul_mem hx hy
    · intro x _ hx
      rw [map_inv]
      exact C.inv_mem hx
  have htop : (⊤ : Subgroup V) ≤ fixV (Subgroup.zpowers t) := by
    rcases hirr.2.2.2 C hCst bot_le le_top with h | h
    · rw [← commSub_eq_bot_iff]
      exact h
    · rw [← h]
      exact hCfix
  ext v
  have := (mem_fixV.mp (htop (Subgroup.mem_top v))) t (Subgroup.mem_zpowers t)
  simpa using this

theorem le_mParam_of_isNaturalClassicalModule [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X H : Subgroup (MulAut V)} {k : ℕ} (hHX : H ≤ X) (hnorm : (H.subgroupOf X).Normal)
    (hirr : IsIrrOn H ⊤ ⊥) (hnat : IsNaturalClassicalModule H k) (heven : Even (Nat.card X)) :
    k ≤ E3.mParam X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold E3.mParam
  rw [if_pos heven]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 (even_iff_two_dvd.mp heven)
  refine le_csInf ⟨_, (x : MulAut V), x.2, by rw [Subgroup.orderOf_coe, hx], rfl⟩ ?_
  rintro _ ⟨t, htX, ht2, rfl⟩
  have htN : t ∈ normalizer (H : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := hnorm.conj_mem ⟨h, hHX hh⟩ (Subgroup.mem_subgroupOf.mpr hh) ⟨t, htX⟩
      exact Subgroup.mem_subgroupOf.mp this
    · intro hh
      have := hnorm.conj_mem ⟨t * h * t⁻¹, hHX hh⟩ (Subgroup.mem_subgroupOf.mpr hh)
        ⟨t, htX⟩⁻¹
      have h' := Subgroup.mem_subgroupOf.mp this
      simpa [mul_assoc] using h'
  refine kNatInvol_holds V H k t hnat htN ht2 ?_
  by_contra hall
  push Not at hall
  have ht1 : t = 1 := eq_one_of_commute_of_isIrrOn hV hirr (by rw [← ht2]; exact pow_orderOf_eq_one t)
    fun h hh => by
      have := hall h hh
      calc t * h = t * h * t⁻¹ * t := by group
        _ = h * t := by rw [this]
  rw [ht1, orderOf_one] at ht2
  exact absurd ht2 (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
