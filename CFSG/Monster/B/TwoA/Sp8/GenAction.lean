
module


public import CFSG.Monster.B.TwoA.Sp8.GenActionImage

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

theorem aEquiv_ne_one
    {v : V8} (h : v ≠ 0) : (aEquiv (Multiplicative.ofAdd v) : Dfull) ≠ 1 := by
  intro h1
  apply h
  apply aEquiv_coe_injective
  rw [h1, ofAdd_zero, map_one, OneMemClass.coe_one]

theorem toAdd_ne_zero_of_ne_one
    {x : Dfull} (hx : x ∈ A8) (h1 : x ≠ 1) :
    Multiplicative.toAdd (aEquiv.symm ⟨x, hx⟩) ≠ 0 := by
  intro h
  apply h1
  have e : aEquiv (aEquiv.symm ⟨x, hx⟩) = ⟨x, hx⟩ := MulEquiv.apply_symm_apply _ _
  rw [← ofAdd_toAdd (aEquiv.symm ⟨x, hx⟩), h, ofAdd_zero, map_one] at e
  exact (congrArg Subtype.val e).symm

theorem coe_aEquiv_symm
    {x : Dfull} (hx : x ∈ A8) :
    (aEquiv (Multiplicative.ofAdd (Multiplicative.toAdd (aEquiv.symm ⟨x, hx⟩))) : Dfull) = x := by
  rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem Xgrp_transitive
    {x y : Dfull} (hx : x ∈ A8) (hy : y ∈ A8) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : ∃ g ∈ Xgrp, g * x * g⁻¹ = y := by
  obtain ⟨f₁, hf₁, e₁⟩ := exists_conjImage_X (toAdd_ne_zero_of_ne_one hx hx1)
  obtain ⟨f₂, hf₂, e₂⟩ := exists_conjImage_X (toAdd_ne_zero_of_ne_one hy hy1)
  have hf : f₂ * f₁⁻¹ ∈ (Xgrp.subgroupOf NA8).map conjHom := by
    rw [conjImage_X]
    exact Subgroup.mul_mem _ hf₂ (Subgroup.inv_mem _ hf₁)
  obtain ⟨n, hn, hnf⟩ := hf
  refine ⟨n, Subgroup.mem_subgroupOf.1 hn, ?_⟩
  have hv : f₁⁻¹ (Multiplicative.toAdd (aEquiv.symm ⟨x, hx⟩)) = Pi.single 0 1 := by
    rw [← e₁]
    exact f₁.symm_apply_apply _
  have hnv : conjHom n (Multiplicative.toAdd (aEquiv.symm ⟨x, hx⟩)) =
      Multiplicative.toAdd (aEquiv.symm ⟨y, hy⟩) := by
    rw [hnf, LinearEquiv.mul_apply, hv, e₂]
  have h := aEquiv_conjHom n (Multiplicative.toAdd (aEquiv.symm ⟨x, hx⟩))
  rw [hnv, coe_aEquiv_symm hy, coe_aEquiv_symm hx] at h
  exact h.symm

theorem bA_conj
    {g : Dfull} (hg : g ∈ Xgrp) {x y x' y' : A8}
    (hx : (x' : Dfull) = g * x * g⁻¹) (hy : (y' : Dfull) = g * y * g⁻¹) : bA x' y' = bA x y := by
  set n : NA8 := ⟨g, Xgrp_le_normalizer hg⟩
  have hiso := TauCeti.BilinForm.mem_isometryGroup_iff.1
    (conjImage_X_le ⟨n, Subgroup.mem_subgroupOf.2 hg, rfl⟩)
  have ex : Multiplicative.toAdd (aEquiv.symm x') =
      conjHom n (Multiplicative.toAdd (aEquiv.symm x)) := by
    apply aEquiv_coe_injective
    rw [aEquiv_conjHom, ofAdd_toAdd, ofAdd_toAdd, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, hx]
  have ey : Multiplicative.toAdd (aEquiv.symm y') =
      conjHom n (Multiplicative.toAdd (aEquiv.symm y)) := by
    apply aEquiv_coe_injective
    rw [aEquiv_conjHom, ofAdd_toAdd, ofAdd_toAdd, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, hy]
  rw [bA, bA, ex, ey]
  exact hiso _ _

theorem short_symplectic_eight_generator_action :
    H1 ≤ Subgroup.normalizer (A8 : Set Dfull) ∧ Xgrp ≤ Subgroup.normalizer (A8 : Set Dfull) ∧
    (∀ (n : Subgroup.normalizer (A8 : Set Dfull)) (v : Fin 8 → ZMod 2),
      (aEquiv (Multiplicative.ofAdd (conjHom n v)) : Dfull) =
        n * aEquiv (Multiplicative.ofAdd v) * (n : Dfull)⁻¹) ∧
    (aEquiv (Multiplicative.ofAdd (Pi.single 0 1)) : Dfull) = xhat ∧
    b0.Nondegenerate ∧ b0.IsAlt ∧
    (∀ g ∈ Xgrp, ∀ x y x' y' : A8, (x' : Dfull) = g * x * g⁻¹ → (y' : Dfull) = g * y * g⁻¹ →
      bA x' y' = bA x y) ∧
    (Xgrp.subgroupOf (Subgroup.normalizer (A8 : Set Dfull))).map conjHom ≤
      TauCeti.BilinForm.isometryGroup b0 ∧
    SpX = TauCeti.BilinForm.isometryGroup b0 ⊓
      MulAction.stabilizer ((Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))
        (Pi.single 0 1 : Fin 8 → ZMod 2) ∧
    (H1.subgroupOf (Subgroup.normalizer (A8 : Set Dfull))).map conjHom = SpX ∧
    Nat.card SpX = 185794560 ∧ 185794560 = 2 ^ 7 * 1451520 ∧
    Nat.card ((Ehat.subgroupOf (Subgroup.normalizer (A8 : Set Dfull))).map conjHom) = 128 ∧
    (∀ x ∈ A8, ∀ y ∈ A8, x ≠ 1 → y ≠ 1 → ∃ g ∈ Xgrp, g * x * g⁻¹ = y) :=
  ⟨H1_le_normalizer, Xgrp_le_normalizer, aEquiv_conjHom, aEquiv_e0, b0_nondegenerate, b0_isAlt,
    fun _ hg _ _ _ _ hx hy => bA_conj hg hx hy, conjImage_X_le, rfl, conjImage_H1_eq,
    natCard_SpX, by norm_num, natCard_conjImage_Ehat,
    fun _ hx _ hy hx1 hy1 => Xgrp_transitive hx hy hx1 hy1⟩

end CFSG.Monster.B.TwoA.Sp8
