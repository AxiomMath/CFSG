module

public import CFSG.Quasithin.Background.HSL3S77Model
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.H.S77

open Matrix

theorem th0_pow_three : th0 ^ 3 = 1 := by decide +kernel

theorem th0_ne_one : th0 ≠ 1 := by decide +kernel

theorem th0_inv : th0⁻¹ = th0 * th0 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_three, th0_pow_three]

abbrev th0d : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ((th0 * th0 : SL32) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ

theorem dact_th0 (y : Vec) : dact th0 y = th0d *ᵥ y := by rw [dact, th0_inv]

theorem fix_th0 : ∀ x : Vec, act th0 x = x ↔ x = 0 ∨ x = e1 := by decide +kernel

theorem dfix_th0 : ∀ y : Vec, th0d *ᵥ y = y ↔ y = 0 ∨ y = e1 := by decide +kernel

theorem vm_th0 : ∀ x : Vec, x 0 = 0 → (act th0 x) 0 = 0 := by decide +kernel

theorem dvm_th0 : ∀ y : Vec, y 0 = 0 → (th0d *ᵥ y) 0 = 0 := by decide +kernel

theorem vm_surj : ∀ w : Vec, w 0 = 0 → ∃ v : Vec, v 0 = 0 ∧ act th0 v + v = w := by
  decide +kernel

theorem dvm_surj : ∀ w : Vec, w 0 = 0 → ∃ v : Vec, v 0 = 0 ∧ th0d *ᵥ v + v = w := by
  decide +kernel

theorem vm_card : (Finset.univ.filter (fun q : Vec × Vec => InVm q)).card = 16 := by
  decide +kernel

theorem exists_conj_th0 {g : SL32} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∃ h : SL32, h * g * h⁻¹ = th0 ∨ h * g * h⁻¹ = th0 * th0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card SL32 = 168 := by
    have h2 : (∏ i : Fin 3, (Fintype.card (ZMod 2) ^ 3 - Fintype.card (ZMod 2) ^ (i : ℕ))) /
        (Fintype.card (ZMod 2) - 1) = 168 := by
      rw [Fin.prod_univ_three, ZMod.card]
      norm_num
    exact (Matrix.card_SL_field (𝔽 := ZMod 2) 3).trans h2
  have hsyl : ∀ x : SL32, x ^ 3 = 1 → x ≠ 1 →
      IsPGroup 3 (Subgroup.zpowers x) ∧ ¬ 3 ∣ (Subgroup.zpowers x).index := by
    intro x hx3 hx1
    have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hc : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hord]
    refine ⟨IsPGroup.of_card (n := 1) (by rw [hc, pow_one]), ?_⟩
    have h := (Subgroup.zpowers x).card_mul_index
    rw [hc, hcard] at h
    omega
  obtain ⟨hp, hi⟩ := hsyl g hg3 hg1
  obtain ⟨hp0, hi0⟩ := hsyl th0 th0_pow_three th0_ne_one
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq SL32 (hp.toSylow hi) (hp0.toSylow hi0)
  have hmem : h * g * h⁻¹ ∈ Subgroup.zpowers th0 := by
    have h1 : h * g * h⁻¹ ∈ ((h • hp.toSylow hi : Sylow 3 SL32) : Subgroup SL32) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have : (MulAut.conj h)⁻¹ • (h * g * h⁻¹) = g := by
        rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
        group
      rw [this]
      exact Subgroup.mem_zpowers g
    rw [hh] at h1
    exact h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : th0 ^ k = th0 ^ (k % 3).toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
    rw [show th0 ^ (3 : ℤ) = 1 by rw [zpow_ofNat, th0_pow_three], one_zpow, mul_one]
  have hlt : (k % 3).toNat < 3 := by omega
  refine ⟨h, ?_⟩
  rw [← hk, hk']
  interval_cases hn : (k % 3).toNat
  · exfalso
    apply hg1
    have h2 : h * g * h⁻¹ = 1 := by rw [← hk, hk', pow_zero]
    have : g = h⁻¹ * (h * g * h⁻¹) * h := by group
    rw [this, h2]
    group
  · left
    rw [pow_one]
  · right
    rw [pow_two]

end CFSG.Quasithin.H.S77
