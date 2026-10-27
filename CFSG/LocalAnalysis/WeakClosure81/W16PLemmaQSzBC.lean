module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix

variable {Γ : Type*} [Group Γ] {K : Type*} [CommRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def conjCrossed (mm : Γ →* Matrix ι ι K) (δ : Γ → (ι → K)) (g : Γ) : Γ → (ι → K) :=
  fun x => mm g⁻¹ *ᵥ δ (g * x * g⁻¹)

theorem conjCrossed_mul (mm : Γ →* Matrix ι ι K) {δ : Γ → (ι → K)}
    (hδ : ∀ x y, δ (x * y) = δ x + mm x *ᵥ δ y) (g x y : Γ) :
    conjCrossed mm δ g (x * y) = conjCrossed mm δ g x + mm x *ᵥ conjCrossed mm δ g y := by
  unfold conjCrossed
  have h : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
  have hm : mm g⁻¹ * mm (g * x * g⁻¹) = mm x * mm g⁻¹ := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [h, hδ, mulVec_add, mulVec_mulVec, mulVec_mulVec, hm]

theorem conjCrossed_eq_sub (mm : Γ →* Matrix ι ι K) {δ : Γ → (ι → K)} {g x : Γ}
    {n : ι → K} (h : conjCrossed mm δ g x = mm x *ᵥ n - n) :
    δ (g * x * g⁻¹) = mm (g * x * g⁻¹) *ᵥ (mm g *ᵥ n) - mm g *ᵥ n := by
  have h1 : δ (g * x * g⁻¹) = mm g *ᵥ conjCrossed mm δ g x := by
    unfold conjCrossed
    rw [mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, one_mulVec]
  have h2 : mm (g * x * g⁻¹) *ᵥ (mm g *ᵥ n) = mm g *ᵥ (mm x *ᵥ n) := by
    rw [mulVec_mulVec, mulVec_mulVec, ← map_mul, ← map_mul,
      show g * x * g⁻¹ * g = g * x by group]
  rw [h1, h, h2, mulVec_sub]

theorem mulVec_conj_mulVec (mm : Γ →* Matrix ι ι K) {g z : Γ} {n : ι → K}
    (h : mm z *ᵥ n = n) : mm (g * z * g⁻¹) *ᵥ (mm g *ᵥ n) = mm g *ᵥ n := by
  have h2 : mm (g * z * g⁻¹) *ᵥ (mm g *ᵥ n) = mm g *ᵥ (mm z *ᵥ n) := by
    rw [mulVec_mulVec, mulVec_mulVec, ← map_mul, ← map_mul,
      show g * z * g⁻¹ * g = g * z by group]
  rw [h2, h]

end CFSG.LocalAnalysis.WeakClosure81

end
