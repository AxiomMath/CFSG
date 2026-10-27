module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin

namespace Stellmacher.L3YC

namespace Row18

open Matrix

abbrev SL32 : Type := SpecialLinearGroup (Fin 3) (ZMod 2)

@[expose] def vecStab (a : Fin 3 → ZMod 2) : Subgroup SL32 where
  carrier := {M | M.1 *ᵥ a = a}
  mul_mem' {M N} hM hN := by
    have hM' : M.1 *ᵥ a = a := hM
    have hN' : N.1 *ᵥ a = a := hN
    show (M.1 * N.1) *ᵥ a = a
    rw [← mulVec_mulVec, hN', hM']
  one_mem' := by
    show (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ a = a
    rw [one_mulVec]
  inv_mem' {M} hM := by
    have hM' : M.1 *ᵥ a = a := hM
    show M⁻¹.1 *ᵥ a = a
    have h : (M⁻¹ * M).1 *ᵥ a = a := by
      rw [inv_mul_cancel]
      show (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ a = a
      rw [one_mulVec]
    change (M⁻¹.1 * M.1) *ᵥ a = a at h
    rw [← mulVec_mulVec, hM'] at h
    exact h

@[expose] def covStab (a : Fin 3 → ZMod 2) : Subgroup SL32 where
  carrier := {M | a ᵥ* M.1 = a}
  mul_mem' {M N} hM hN := by
    have hM' : a ᵥ* M.1 = a := hM
    have hN' : a ᵥ* N.1 = a := hN
    show a ᵥ* (M.1 * N.1) = a
    rw [← vecMul_vecMul, hM', hN']
  one_mem' := by
    show a ᵥ* (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = a
    rw [vecMul_one]
  inv_mem' {M} hM := by
    have hM' : a ᵥ* M.1 = a := hM
    show a ᵥ* M⁻¹.1 = a
    have h : a ᵥ* (M * M⁻¹).1 = a := by
      rw [mul_inv_cancel]
      show a ᵥ* (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = a
      rw [vecMul_one]
    change a ᵥ* (M.1 * M⁻¹.1) = a at h
    rw [← vecMul_vecMul, hM'] at h
    exact h

instance (a : Fin 3 → ZMod 2) : DecidablePred (· ∈ vecStab a) := fun M =>
  inferInstanceAs (Decidable (M.1 *ᵥ a = a))

instance (a : Fin 3 → ZMod 2) : DecidablePred (· ∈ covStab a) := fun M =>
  inferInstanceAs (Decidable (a ᵥ* M.1 = a))

@[expose] def e1 : Fin 3 → ZMod 2 := ![1, 0, 0]

@[expose] def e3 : Fin 3 → ZMod 2 := ![0, 0, 1]

@[expose] def borel : Subgroup SL32 := vecStab e1 ⊓ covStab e3

instance : DecidablePred (· ∈ borel) := fun M =>
  decidable_of_iff (M ∈ vecStab e1 ∧ M ∈ covStab e3) Subgroup.mem_inf.symm

theorem card_SL32 : Nat.card SL32 = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_vecStab : Nat.card (vecStab e1) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_covStab : Nat.card (covStab e3) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_borel : Nat.card borel = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem index_vecStab : (vecStab e1).index = 7 := by
  have h := Subgroup.card_mul_index (vecStab e1)
  rw [card_vecStab, card_SL32] at h
  omega

theorem index_covStab : (covStab e3).index = 7 := by
  have h := Subgroup.card_mul_index (covStab e3)
  rw [card_covStab, card_SL32] at h
  omega

theorem index_borel : borel.index = 21 := by
  have h := Subgroup.card_mul_index borel
  rw [card_borel, card_SL32] at h
  omega

theorem vecStab_ne_covStab : vecStab e1 ≠ covStab e3 := by
  intro h
  have h1 : borel = vecStab e1 := by
    unfold borel
    rw [← h]
    exact inf_idem _
  have := congrArg (fun A : Subgroup SL32 => Nat.card A) h1
  rw [card_borel, card_vecStab] at this
  omega

theorem borel_isPGroup : IsPGroup 2 borel := by
  have h : Nat.card borel = 2 ^ 3 := by rw [card_borel]; norm_num
  exact IsPGroup.of_card h

theorem exists_two_overgroups {Λ : Type*} [Group Λ] [Finite Λ] (ψ : Λ →* SL32)
    (hψ : Function.Surjective ψ) {S : Subgroup Λ} (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) :
    ∃ Z₁ Z₂ : Subgroup Λ, S ≤ Z₁ ∧ S ≤ Z₂ ∧ Z₁ ≠ Z₂ ∧ Z₁.index = 7 ∧ Z₂.index = 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpD : IsPGroup 2 (S.map ψ) := hS2.map ψ
  have hiD : ¬ 2 ∣ (S.map ψ).index := fun h => hSi (h.trans (Subgroup.index_map_dvd S hψ))
  have hiB : ¬ 2 ∣ borel.index := by rw [index_borel]; omega
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL32 (borel_isPGroup.toSylow hiB) (hpD.toSylow hiD)
  have hDB : S.map ψ = borel.map (MulAut.conj g).toMonoidHom :=
    (congrArg (fun T : Sylow 2 SL32 => (T : Subgroup SL32)) hg).symm
  have hc : Function.Bijective (MulAut.conj g).toMonoidHom := (MulAut.conj g).bijective
  have hB1 : borel ≤ vecStab e1 := inf_le_left
  have hB2 : borel ≤ covStab e3 := inf_le_right
  refine ⟨((vecStab e1).map (MulAut.conj g).toMonoidHom).comap ψ,
    ((covStab e3).map (MulAut.conj g).toMonoidHom).comap ψ, ?_, ?_, ?_, ?_, ?_⟩
  · refine (Subgroup.le_comap_map ψ S).trans (Subgroup.comap_mono ?_)
    rw [hDB]
    exact Subgroup.map_mono hB1
  · refine (Subgroup.le_comap_map ψ S).trans (Subgroup.comap_mono ?_)
    rw [hDB]
    exact Subgroup.map_mono hB2
  · intro h
    have h1 := Subgroup.comap_injective hψ h
    have h2 : vecStab e1 = covStab e3 := Subgroup.map_injective hc.1 h1
    exact vecStab_ne_covStab h2
  · rw [Subgroup.index_comap_of_surjective _ hψ, Subgroup.index_map_of_bijective hc, index_vecStab]
  · rw [Subgroup.index_comap_of_surjective _ hψ, Subgroup.index_map_of_bijective hc, index_covStab]

end Row18

end Stellmacher.L3YC

end CFSG.Quasithin
