module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ModelAlgDefs

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix

variable {K : Type*} [Field K]

theorem rhoSL_apply (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : UTilde K) :
    rhoSL K g v =
      ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v.1, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v.2) :=
  rfl

theorem sigmaPerm_apply (σ : RingAut K) (v : UTilde K) :
    sigmaPerm K σ v = (fun i => σ (v.1 i), fun i => σ (v.2 i)) :=
  rfl

theorem bPerm_apply (B : GL (Fin 2) K) (v : UTilde K) :
    bPerm K B v = (((B : Matrix (Fin 2) (Fin 2) K) 0 0) • v.1 + ((B : Matrix (Fin 2) (Fin 2) K) 0 1) • v.2,
      ((B : Matrix (Fin 2) (Fin 2) K) 1 0) • v.1 + ((B : Matrix (Fin 2) (Fin 2) K) 1 1) • v.2) :=
  rfl

theorem sigmaPerm_mul (σ τ : RingAut K) :
    sigmaPerm K (σ * τ) = sigmaPerm K σ * sigmaPerm K τ := by
  rfl

theorem sigmaPerm_one : sigmaPerm K (1 : RingAut K) = 1 := rfl

theorem sigmaPerm_inv_mul (σ : RingAut K) : sigmaPerm K σ⁻¹ * sigmaPerm K σ = 1 := by
  rw [← sigmaPerm_mul, inv_mul_cancel, sigmaPerm_one]

theorem sigmaPerm_mul_inv (σ : RingAut K) : sigmaPerm K σ * sigmaPerm K σ⁻¹ = 1 := by
  rw [← sigmaPerm_mul, mul_inv_cancel, sigmaPerm_one]

private theorem mulVec_map_aux (σ : RingAut K) (M : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) :
    (fun i => σ ((M *ᵥ v) i)) = M.map σ *ᵥ (fun i => σ (v i)) := by
  funext i
  exact RingHom.map_mulVec (σ : K →+* K) M v i

theorem sigmaPerm_rho (σ : RingAut K) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    sigmaPerm K σ * rhoSL K g = rhoSL K (slMap σ g) * sigmaPerm K σ := by
  refine Equiv.ext fun v => ?_
  simp only [Equiv.Perm.mul_apply, rhoSL_apply, sigmaPerm_apply]
  exact Prod.ext (mulVec_map_aux σ _ v.1) (mulVec_map_aux σ _ v.2)

theorem bPerm_rho (B : GL (Fin 2) K) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    bPerm K B * rhoSL K g = rhoSL K g * bPerm K B := by
  refine Equiv.ext fun v => ?_
  simp only [Equiv.Perm.mul_apply, rhoSL_apply, bPerm_apply, Matrix.mulVec_add, Matrix.mulVec_smul]

theorem bPerm_mul (B B' : GL (Fin 2) K) : bPerm K (B * B') = bPerm K B * bPerm K B' := by
  refine Equiv.ext fun v => ?_
  simp only [Equiv.Perm.mul_apply, bPerm_apply, Units.val_mul]
  exact (mix_mul_aux _ _ v).symm

theorem glMap_coe_apply (σ : RingAut K) (B : GL (Fin 2) K) (i j : Fin 2) :
    ((glMap K σ B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
      σ ((B : Matrix (Fin 2) (Fin 2) K) i j) :=
  rfl

theorem sigmaPerm_bPerm (σ : RingAut K) (B : GL (Fin 2) K) :
    sigmaPerm K σ * bPerm K B = bPerm K (glMap K σ B) * sigmaPerm K σ := by
  refine Equiv.ext fun v => ?_
  simp only [Equiv.Perm.mul_apply, bPerm_apply, sigmaPerm_apply, glMap_coe_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]

theorem phi_mul (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) K) (σ₁ σ₂ : RingAut K)
    (B₁ B₂ : GL (Fin 2) K) :
    phi K g₁ σ₁ B₁ * phi K g₂ σ₂ B₂ =
      phi K (g₁ * slMap σ₁ g₂) (σ₁ * σ₂) (glMap K σ₂⁻¹ B₁ * B₂) := by
  have he : bPerm K B₁ * sigmaPerm K σ₂ = sigmaPerm K σ₂ * bPerm K (glMap K σ₂⁻¹ B₁) := by
    have hc := sigmaPerm_bPerm σ₂⁻¹ B₁
    calc bPerm K B₁ * sigmaPerm K σ₂
        = (sigmaPerm K σ₂ * sigmaPerm K σ₂⁻¹) * bPerm K B₁ * sigmaPerm K σ₂ := by
          rw [sigmaPerm_mul_inv, one_mul]
      _ = sigmaPerm K σ₂ * (sigmaPerm K σ₂⁻¹ * bPerm K B₁) * sigmaPerm K σ₂ := by
          simp only [mul_assoc]
      _ = sigmaPerm K σ₂ * (bPerm K (glMap K σ₂⁻¹ B₁) * sigmaPerm K σ₂⁻¹) * sigmaPerm K σ₂ := by
          rw [hc]
      _ = sigmaPerm K σ₂ * bPerm K (glMap K σ₂⁻¹ B₁) * (sigmaPerm K σ₂⁻¹ * sigmaPerm K σ₂) := by
          simp only [mul_assoc]
      _ = sigmaPerm K σ₂ * bPerm K (glMap K σ₂⁻¹ B₁) := by
          rw [sigmaPerm_inv_mul, mul_one]
  unfold phi
  calc rhoSL K g₁ * sigmaPerm K σ₁ * bPerm K B₁ * (rhoSL K g₂ * sigmaPerm K σ₂ * bPerm K B₂)
      = rhoSL K g₁ * sigmaPerm K σ₁ * (bPerm K B₁ * rhoSL K g₂) * sigmaPerm K σ₂ * bPerm K B₂ := by
          simp only [mul_assoc]
    _ = rhoSL K g₁ * sigmaPerm K σ₁ * (rhoSL K g₂ * bPerm K B₁) * sigmaPerm K σ₂ * bPerm K B₂ := by
          rw [bPerm_rho]
    _ = rhoSL K g₁ * (sigmaPerm K σ₁ * rhoSL K g₂) * bPerm K B₁ * sigmaPerm K σ₂ * bPerm K B₂ := by
          simp only [mul_assoc]
    _ = rhoSL K g₁ * (rhoSL K (slMap σ₁ g₂) * sigmaPerm K σ₁) * bPerm K B₁ * sigmaPerm K σ₂
          * bPerm K B₂ := by
          rw [sigmaPerm_rho]
    _ = rhoSL K (g₁ * slMap σ₁ g₂) * sigmaPerm K σ₁ * (bPerm K B₁ * sigmaPerm K σ₂)
          * bPerm K B₂ := by
          rw [map_mul]
          simp only [mul_assoc]
    _ = rhoSL K (g₁ * slMap σ₁ g₂) * sigmaPerm K σ₁ * (sigmaPerm K σ₂ * bPerm K (glMap K σ₂⁻¹ B₁))
          * bPerm K B₂ := by
          rw [he]
    _ = rhoSL K (g₁ * slMap σ₁ g₂) * (sigmaPerm K σ₁ * sigmaPerm K σ₂)
          * (bPerm K (glMap K σ₂⁻¹ B₁) * bPerm K B₂) := by
          simp only [mul_assoc]
    _ = rhoSL K (g₁ * slMap σ₁ g₂) * sigmaPerm K (σ₁ * σ₂) * bPerm K (glMap K σ₂⁻¹ B₁ * B₂) := by
          rw [sigmaPerm_mul, bPerm_mul]

end CFSG.Quasithin.Vol2.Ch10Reselect
