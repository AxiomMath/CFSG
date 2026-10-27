module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3Sz
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Ord

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P3

theorem eq_or_eq_of_sq_eq_one {H : Type*} [Group H] [Finite H] [IsCyclic H] {a b c : H}
    (hab : a ≠ b) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) : c = a ∨ c = b := by
  classical
  have := Fintype.ofFinite H
  by_contra h
  push Not at h
  have hcard := IsCyclic.card_pow_eq_one_le (α := H) (n := 2) (by norm_num)
  have hsub : ({a, b, c} : Finset H) ⊆ Finset.univ.filter (fun x => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3 : ({a, b, c} : Finset H).card = 3 :=
    Finset.card_eq_three.2 ⟨a, b, c, hab, fun hac => h.1 hac.symm, fun hbc => h.2 hbc.symm, rfl⟩
  have := Finset.card_le_card hsub
  omega

variable {G : Type*} [Group G]

theorem conj_inv_conj_inv {x w z : G} (hx : x ^ 5 = 1) (hw : w⁻¹ * x * w = x ^ 2)
    (hz2 : z * z = 1) (hz : z * x * z = x⁻¹) : (w⁻¹ * z * w) * x * (w⁻¹ * z * w) = x⁻¹ := by
  have h3 := conj_eq_pow_three hx hw
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzc : z * x ^ 3 * z = (z * x * z) ^ 3 := by
    have := conj_pow (a := z) (b := x) (i := 3)
    rw [hzi] at this
    exact this.symm
  have hwc : w⁻¹ * (x⁻¹) ^ 3 * w = (w⁻¹ * x⁻¹ * w) ^ 3 := by
    have := conj_pow (a := w⁻¹) (b := x⁻¹) (i := 3)
    simpa using this.symm
  have hwi : w⁻¹ * x⁻¹ * w = (x ^ 2)⁻¹ := by rw [← hw]; group
  have h6 : ((x ^ 2)⁻¹) ^ 3 = x⁻¹ := by
    rw [inv_pow, ← pow_mul, show 2 * 3 = 5 + 1 by norm_num, pow_succ, hx, one_mul]
  calc (w⁻¹ * z * w) * x * (w⁻¹ * z * w) = w⁻¹ * (z * (w * x * w⁻¹) * z) * w := by group
    _ = w⁻¹ * (z * x ^ 3 * z) * w := by rw [h3]
    _ = w⁻¹ * (x⁻¹) ^ 3 * w := by rw [hzc, hz]
    _ = x⁻¹ := by rw [hwc, hwi, h6]

theorem sq_conj_eq_inv {x w : G} (hx : x ^ 5 = 1) (hw : w⁻¹ * x * w = x ^ 2) :
    w ^ 2 * x * (w ^ 2)⁻¹ = x⁻¹ := by
  have h3 := conj_eq_pow_three hx hw
  calc w ^ 2 * x * (w ^ 2)⁻¹ = w * (w * x * w⁻¹) * w⁻¹ := by simp [pow_two, mul_assoc]
    _ = w * x ^ 3 * w⁻¹ := by rw [h3]
    _ = (w * x * w⁻¹) ^ 3 := by rw [conj_pow]
    _ = (x ^ 3) ^ 3 := by rw [h3]
    _ = x⁻¹ := by
      rw [← pow_mul, show 3 * 3 = 5 + 4 by norm_num, pow_add, hx, one_mul]
      have : x ^ 4 * x = 1 := by rw [← pow_succ, show 4 + 1 = 5 by norm_num, hx]
      exact eq_inv_of_mul_eq_one_left this

variable {V : Type*} [MulAction G V] {Γ : SimpleGraph V}

theorem mem_calpha_of_comm {L : ZLab Γ G} {F : FanTree Γ G} (h : Fan71c F L) {α : V}
    (D : D10Set L α) {g : G} (hgx : g * D.x = D.x * g) (hgβ : g • D.beta 0 = D.beta 0) :
    g ∈ D.calpha := by
  refine Subgroup.mem_inf.2 ⟨mem_nbrStab.2 fun w hw => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := D.exists_beta_eq F h hw
    have hi : (D.x ^ i.val)⁻¹ • D.beta 0 = D.beta i := by
      have := D.x_pow_inv_smul_vert F h i.val 0 (m := 1) (by norm_num)
      rwa [zero_add, Fin.cast_val_eq_self] at this
    have hc : g * (D.x ^ i.val)⁻¹ = (D.x ^ i.val)⁻¹ * g :=
      ((show Commute g D.x from hgx).pow_right i.val).inv_right.eq
    rw [← hi, ← mul_smul, hc, mul_smul, hgβ]
  · rw [Subgroup.mem_centralizer_iff]
    intro h' hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hgx.symm

end Sec8P3

end CFSG.Quasithin.Fan86
