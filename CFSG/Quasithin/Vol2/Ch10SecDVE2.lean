module

public import CFSG.Quasithin.Vol2.Ch10SecDVE
public import CFSG.Quasithin.Vol2.Ch10SecC8V1
public import CFSG.Quasithin.Vol2.Ch10SecDBasic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fpf_of_odd (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥)
    {v1 x : G} (hv1 : v1 ∈ fsuUL T L I) (hv11 : v1 ≠ 1)
    (hxN : x ∈ Subgroup.normalizer (fsuUL T L I : Set G)) (hxo : Odd (orderOf x))
    (hxv1 : x * v1 * x⁻¹ = v1) (hxC : x ∉ Subgroup.centralizer (fsuUL T L I : Set G))
    {u : G} (hu : u ∈ fsuUL T L I) (hxu : x * u * x⁻¹ = u ∨ x * u * x⁻¹ = u * v1) :
    u = 1 ∨ u = v1 := by
  by_contra hne
  push Not at hne
  have h8 := card_V1 h3 hc
  have h3' := h3
  obtain ⟨-, hcm, -⟩ := h3'
  set c : MulAut ↥(fsuUL T L I) := conjAct (fsuUL T L I) ⟨x, hxN⟩ with hcdef
  have hcv : ∀ y : ↥(fsuUL T L I), ((c y : ↥(fsuUL T L I)) : G) = x * y * x⁻¹ := fun y =>
    A1b.conjAct_coe (fsuUL T L I) ⟨x, hxN⟩ y
  have hodd : Odd (orderOf c) := by
    have h1 : c ^ orderOf x = 1 := by
      rw [hcdef, ← map_pow]
      have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (fsuUL T L I : Set G))) ^ orderOf x = 1 :=
        Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this, map_one]
    exact Odd.of_dvd_nat hxo (orderOf_dvd_of_pow_eq_one h1)
  have hc1 : c ⟨v1, hv1⟩ = ⟨v1, hv1⟩ := Subtype.ext (by rw [hcv]; exact hxv1)
  have hc2 : (c ^ 2) ⟨u, hu⟩ = ⟨u, hu⟩ := by
    apply Subtype.ext
    rw [pow_two, MulAut.mul_apply, hcv, hcv]
    show x * (x * u * x⁻¹) * x⁻¹ = u
    rcases hxu with h1 | h1
    · rw [h1, h1]
    · have e : x * (u * v1) * x⁻¹ = (x * u * x⁻¹) * (x * v1 * x⁻¹) := by group
      rw [h1, e, h1, hxv1, mul_assoc, ← pow_two,
        (SecA.isElemAbelian_fsuVM h).2 v1 (V1_le_V hv1), mul_one]
  have hcu : c ⟨u, hu⟩ = ⟨u, hu⟩ := by
    obtain ⟨k, hk⟩ := hodd
    have hpow : ∀ n : ℕ, ((c ^ 2) ^ n) ⟨u, hu⟩ = ⟨u, hu⟩ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hc2, ih]
    have e : c = (c ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf c + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [e]
    exact hpow _
  have hc1' := eq_one_of_odd_of_fix (SecC.sq_eq_one_fsuUL h) h8 hodd hc1 hcu
    (fun h1 => hv11 (congrArg Subtype.val h1)) (fun h1 => hne.1 (congrArg Subtype.val h1))
    (fun h1 => hne.2 (congrArg Subtype.val h1).symm)
  exact hxC (A1b.conjAct_eq_one_iff.mp hc1')

end CFSG.Quasithin.Vol2.Ch10.SecD
