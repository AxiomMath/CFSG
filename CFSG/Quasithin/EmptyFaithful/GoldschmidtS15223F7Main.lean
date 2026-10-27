module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223F7Fin
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.S15223

open Equiv Equiv.Perm
open scoped Pointwise

theorem F7.eq_one_of_mem_isPGroup_two {J : Subgroup (Perm (Fin 7))} (hJ : IsPGroup 2 J)
    {z : Perm (Fin 7)} (hz : z ∈ J) (h3 : z ^ 3 = 1) : z = 1 := by
  obtain ⟨k, hk⟩ := hJ ⟨z, hz⟩
  have h2 : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hd : orderOf z ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

theorem false_of_swap_normalized_by_nine {Y J : Subgroup (Equiv.Perm (Fin 7))}
    (hY : Nat.card Y = 9) (hY3 : IsPGroup 3 Y) (hJ : IsPGroup 2 J)
    (hYJ : Y ≤ Subgroup.normalizer (J : Set (Equiv.Perm (Fin 7))))
    (hswap : ∃ a b : Fin 7, a ≠ b ∧ Equiv.swap a b ∈ J) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b, hab, hmem⟩ := hswap
  let PY : Sylow 3 (Perm (Fin 7)) := hY3.toSylow (F7.not_dvd_index hY)
  let P0 : Sylow 3 (Perm (Fin 7)) :=
    F7.isPGroup_y0.toSylow (F7.not_dvd_index F7.card_y0)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 7)) P0 PY
  have hconj : ∀ x ∈ F7.y0, g * x * g⁻¹ ∈ Y := by
    intro x hx
    have h1 := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P0 : Subgroup (Perm (Fin 7))) hx
    have h2 : (MulAut.conj g • (P0 : Subgroup (Perm (Fin 7)))) = Y := by
      rw [← Sylow.coe_subgroup_smul, hg]
      rfl
    rw [h2] at h1
    exact h1
  have hab' : g⁻¹ a ≠ g⁻¹ b := fun h => hab (g⁻¹.injective h)
  obtain ⟨y₀, hy₀L, h3, h1⟩ := F7.exists_order_three _ _ hab'
  have ht : swap a b = g * swap (g⁻¹ a) (g⁻¹ b) * g⁻¹ := by
    rw [← Equiv.swap_apply_apply]
    simp
  generalize swap (g⁻¹ a) (g⁻¹ b) = s at ht h3 h1
  have hyY : g * y₀ * g⁻¹ ∈ Y := hconj y₀ (F7.mem_y0.mpr hy₀L)
  have hyt : g * y₀ * g⁻¹ * swap a b * (g * y₀ * g⁻¹)⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp (hYJ hyY) (swap a b)).mp hmem
  have hz : swap a b * (g * y₀ * g⁻¹ * swap a b * (g * y₀ * g⁻¹)⁻¹) ∈ J := J.mul_mem hmem hyt
  have e : swap a b * (g * y₀ * g⁻¹ * swap a b * (g * y₀ * g⁻¹)⁻¹) =
      g * (s * (y₀ * s * y₀⁻¹)) * g⁻¹ := by
    rw [ht]
    group
  have hz3 : (swap a b * (g * y₀ * g⁻¹ * swap a b * (g * y₀ * g⁻¹)⁻¹)) ^ 3 = 1 := by
    rw [e, conj_pow, h3, mul_one, mul_inv_cancel]
  have hz1 : swap a b * (g * y₀ * g⁻¹ * swap a b * (g * y₀ * g⁻¹)⁻¹) ≠ 1 := by
    intro h
    rw [e] at h
    apply h1
    simpa using h
  exact hz1 (F7.eq_one_of_mem_isPGroup_two hJ hz hz3)

end CFSG.Quasithin.S15223
