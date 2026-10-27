module

public import CFSG.LieType.Chevalley.RankOneGaussian

public noncomputable section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.LieType.Chevalley Matrix

variable {K : Type*} [Field K]

theorem WSL_eq_uvu : (WSL : SL2 K) = uSL 1 * vSL (-1) * uSL 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, coe_vSL, coe_WSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem HSL_mul_WSL_eq (t : Kˣ) :
    (HSL t : SL2 K) * WSL = uSL (t : K) * vSL (-((t⁻¹ : Kˣ) : K)) * uSL (t : K) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, coe_vSL, coe_HSL, coe_WSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem WSL_mul_uSL_mul_inv' (c : K) : (WSL : SL2 K) * uSL c * WSL⁻¹ = vSL (-c) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_WSL,
    coe_uSL, coe_vSL, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem WSL_mul_vSL_mul_inv' (c : K) : (WSL : SL2 K) * vSL c * WSL⁻¹ = uSL (-c) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_WSL,
    coe_uSL, coe_vSL, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem hom_eq_of_uSL_vSL {G : Type*} [Group G] (f g : SL2 K →* G)
    (hu : ∀ s, f (uSL s) = g (uSL s)) (hv : ∀ s, f (vSL s) = g (vSL s)) : f = g := by
  have hW : f WSL = g WSL := by
    rw [WSL_eq_uvu, map_mul, map_mul, map_mul, map_mul, hu, hv]
  refine MonoidHom.ext fun B => ?_
  refine SL2_induction (p := fun B => f B = g B) (fun x y hx hy => by simp [map_mul, hx, hy]) hu
    (fun t => ?_) hW B
  have h := HSL_mul_WSL_eq t
  have h' : (HSL t : SL2 K) = uSL (t : K) * vSL (-((t⁻¹ : Kˣ) : K)) * uSL (t : K) * WSL⁻¹ :=
    eq_mul_inv_of_mul_eq h
  rw [h', map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hu, hv, hW]

theorem map_uSL {K' : Type*} [Field K'] (f : K →+* K') (c : K) :
    Matrix.SpecialLinearGroup.map f (uSL c) = uSL (f c) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uSL]

theorem map_vSL {K' : Type*} [Field K'] (f : K →+* K') (c : K) :
    Matrix.SpecialLinearGroup.map f (vSL c) = vSL (f c) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_vSL]

end CFSG.RankThree.PartOne.KLR
