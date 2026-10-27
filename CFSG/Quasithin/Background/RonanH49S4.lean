module

public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr
open scoped Matrix

@[expose] def affS4 : Fin 4 → Fin 3 → ZMod 2 :=
  ![![1, 0, 0], ![1, 1, 0], ![1, 0, 1], ![1, 1, 1]]

@[expose] def idxS4 (r : Fin 3 → ZMod 2) : Fin 4 :=
  ⟨(if r 1 = 1 then 1 else 0) + (if r 2 = 1 then 2 else 0), by split_ifs <;> omega⟩

theorem affS4_zero : ∀ i : Fin 4, affS4 i 0 = 1 := by decide +kernel

theorem idxS4_affS4 : ∀ i : Fin 4, idxS4 (affS4 i) = i := by decide +kernel

theorem affS4_idxS4 : ∀ r : Fin 3 → ZMod 2, r 0 = 1 → affS4 (idxS4 r) = r := by
  decide +kernel

theorem vecMul_affS4_zero (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h10 : M 1 0 = 0)
    (h20 : M 2 0 = 0) (h00 : M 0 0 = 1) (i : Fin 4) : (affS4 i ᵥ* M) 0 = 1 := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, affS4_zero i, h10, h20, h00]

theorem vecMul_affS4_P1 (k : ↥P1) (i : Fin 4) : (affS4 i ᵥ* mat (k : ↥SL32)) 0 = 1 := by
  obtain ⟨h10, h20, h00⟩ := (mulVec_e0_iff (mat (k : ↥SL32))).1 k.2
  exact vecMul_affS4_zero _ h10 h20 h00 i

theorem affS4_idxS4_vecMul (k : ↥P1) (i : Fin 4) :
    affS4 (idxS4 (affS4 i ᵥ* mat (k : ↥SL32))) = affS4 i ᵥ* mat (k : ↥SL32) :=
  affS4_idxS4 _ (vecMul_affS4_P1 k i)

theorem mat_inv_mul_P1 (g : ↥P1) : mat ((g⁻¹ : ↥P1) : ↥SL32) * mat (g : ↥SL32) = 1 := by
  rw [Subgroup.coe_inv, mat_inv_mul]

theorem mat_mul_inv_P1 (g : ↥P1) : mat (g : ↥SL32) * mat ((g⁻¹ : ↥P1) : ↥SL32) = 1 := by
  rw [Subgroup.coe_inv, mat_mul_inv]

theorem eq_one_of_affS4 : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
    (∀ i : Fin 4, affS4 i ᵥ* M = affS4 i) → M = 1 := by
  decide +kernel

@[expose] noncomputable def permS4 : ↥P1 →* Equiv.Perm (Fin 4) where
  toFun g :=
    { toFun := fun i => idxS4 (affS4 i ᵥ* mat ((g⁻¹ : ↥P1) : ↥SL32))
      invFun := fun i => idxS4 (affS4 i ᵥ* mat (g : ↥SL32))
      left_inv := fun i => by
        change idxS4 (affS4 (idxS4 (affS4 i ᵥ* mat ((g⁻¹ : ↥P1) : ↥SL32)))
          ᵥ* mat (g : ↥SL32)) = i
        rw [affS4_idxS4_vecMul, Matrix.vecMul_vecMul, mat_inv_mul_P1, Matrix.vecMul_one,
          idxS4_affS4]
      right_inv := fun i => by
        change idxS4 (affS4 (idxS4 (affS4 i ᵥ* mat (g : ↥SL32)))
          ᵥ* mat ((g⁻¹ : ↥P1) : ↥SL32)) = i
        rw [affS4_idxS4_vecMul, Matrix.vecMul_vecMul, mat_mul_inv_P1, Matrix.vecMul_one,
          idxS4_affS4] }
  map_one' := Equiv.ext fun i => by
    change idxS4 (affS4 i ᵥ* mat (((1 : ↥P1)⁻¹ : ↥P1) : ↥SL32)) = (1 : Equiv.Perm (Fin 4)) i
    rw [inv_one, OneMemClass.coe_one, mat_one, Matrix.vecMul_one, idxS4_affS4,
      Equiv.Perm.one_apply]
  map_mul' g h := Equiv.ext fun i => by
    change idxS4 (affS4 i ᵥ* mat (((g * h)⁻¹ : ↥P1) : ↥SL32)) =
      idxS4 (affS4 (idxS4 (affS4 i ᵥ* mat ((h⁻¹ : ↥P1) : ↥SL32)))
        ᵥ* mat ((g⁻¹ : ↥P1) : ↥SL32))
    rw [affS4_idxS4_vecMul, mul_inv_rev, Subgroup.coe_mul, mat_mul, Matrix.vecMul_vecMul]

theorem permS4_apply (g : ↥P1) (i : Fin 4) :
    permS4 g i = idxS4 (affS4 i ᵥ* mat ((g⁻¹ : ↥P1) : ↥SL32)) := rfl

theorem permS4_injective : Function.Injective permS4 := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ i : Fin 4, affS4 i ᵥ* mat ((g⁻¹ : ↥P1) : ↥SL32) = affS4 i := by
    intro i
    have h : permS4 g i = (1 : Equiv.Perm (Fin 4)) i :=
      congrArg (fun σ : Equiv.Perm (Fin 4) => σ i) hg
    rw [permS4_apply, Equiv.Perm.one_apply] at h
    have hr := affS4_idxS4_vecMul (g⁻¹) i
    rw [h] at hr
    exact hr.symm
  have hM : mat ((g⁻¹ : ↥P1) : ↥SL32) = 1 := eq_one_of_affS4 _ hfix
  have hg1 : (g⁻¹ : ↥P1) = 1 := Subtype.ext (eq_of_mat_eq (hM.trans mat_one.symm))
  exact inv_eq_one.mp hg1

theorem card_perm_fin4_ronan : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem nonempty_P1_mulEquiv_perm : Nonempty (↥P1 ≃* Equiv.Perm (Fin 4)) :=
  ⟨MulEquiv.ofBijective permS4
    (Function.Injective.bijective_of_nat_card_le permS4_injective
      (card_perm_fin4_ronan.trans card_P1.symm).le)⟩

end CFSG.Quasithin.RonanH49
