module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.Quasithin.H13.L14324

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
@[expose] def slOf (a b c d : F) (h : a * d - b * c = 1) : SL(2, F) :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

theorem sub_eq_add_charTwo (a b : F) : a - b = a + b := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [sub_eq_add_neg, CharTwo.neg_eq]

theorem exists_sl_sum (X : Matrix (Fin 2) (Fin 2) F) :
    ∃ g : Fin 8 → SL(2, F), X = ∑ i, ((g i : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
  have hdet : ∀ a b c d : F, a * d + b * c = 1 → a * d - b * c = 1 := fun a b c d h => by
    rw [sub_eq_add_charTwo]; exact h
  refine ⟨![slOf (X 0 0) 1 1 0 (hdet _ _ _ _ (by ring)), slOf 0 1 1 0 (hdet _ _ _ _ (by ring)),
    slOf 0 1 1 (X 1 1) (hdet _ _ _ _ (by ring)), slOf 0 1 1 0 (hdet _ _ _ _ (by ring)),
    slOf 1 (X 0 1) 0 1 (hdet _ _ _ _ (by ring)), slOf 1 0 0 1 (hdet _ _ _ _ (by ring)),
    slOf 1 0 (X 1 0) 1 (hdet _ _ _ _ (by ring)), slOf 1 0 0 1 (hdet _ _ _ _ (by ring))], ?_⟩
  have h2 : ∀ x : F, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  ext i j
  simp only [Fin.sum_univ_eight, Matrix.add_apply, slOf, Matrix.cons_val, Fin.isValue]
  fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply] <;>
    simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]


theorem eq_mul_of_comm_left (y : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F)
    (hy : ∀ (g : SL(2, F)) X, y ((g : Matrix (Fin 2) (Fin 2) F) * X) = (g : Matrix _ _ F) * y X)
    (X : Matrix (Fin 2) (Fin 2) F) : y X = X * y 1 := by
  obtain ⟨g, rfl⟩ := exists_sl_sum X
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hy (g i) 1
  rwa [mul_one] at this

theorem eq_mul_of_comm_right (y : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F)
    (hy : ∀ (g : SL(2, F)) X, y (X * (g : Matrix (Fin 2) (Fin 2) F)) = y X * (g : Matrix _ _ F))
    (X : Matrix (Fin 2) (Fin 2) F) : y X = y 1 * X := by
  obtain ⟨g, rfl⟩ := exists_sl_sum X
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hy (g i) 1
  rwa [one_mul] at this

theorem eq_smul_of_comm (y : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F)
    (hl : ∀ (g : SL(2, F)) X, y ((g : Matrix (Fin 2) (Fin 2) F) * X) = (g : Matrix _ _ F) * y X)
    (hr : ∀ (g : SL(2, F)) X, y (X * (g : Matrix (Fin 2) (Fin 2) F)) = y X * (g : Matrix _ _ F)) :
    ∀ X, y X = y 1 0 0 • X := by
  have h1 : ∀ X : Matrix (Fin 2) (Fin 2) F, X * y 1 = y 1 * X := fun X => by
    rw [← eq_mul_of_comm_left y hl, ← eq_mul_of_comm_right y hr]
  have hE11 := h1 !![1, 0; 0, 0]
  have hE12 := h1 !![0, 1; 0, 0]
  have hE21 := h1 !![0, 0; 1, 0]
  intro X
  rw [eq_mul_of_comm_left y hl X]
  have hR : y 1 = y 1 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have e11 := congrFun (congrFun hE11 0) 1
    have e12 := congrFun (congrFun hE12 0) 0
    have e12' := congrFun (congrFun hE12 0) 1
    have e21 := congrFun (congrFun hE21 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e11 e12 e12' e21
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> grind
  conv_lhs => rw [hR]
  rw [Matrix.mul_smul, Matrix.mul_one]


omit [CharP F 2] in
theorem exists_inner_of_algEquiv (φ : Matrix (Fin 2) (Fin 2) F ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) :
    ∃ P Pinv : Matrix (Fin 2) (Fin 2) F, P * Pinv = 1 ∧ Pinv * P = 1 ∧ ∀ X, φ X = P * X * Pinv := by
  let f : Module.End F (Fin 2 → F) ≃ₐ[F] Module.End F (Fin 2 → F) :=
    (Matrix.toLinAlgEquiv'.symm.trans φ).trans Matrix.toLinAlgEquiv'
  obtain ⟨T, hT⟩ := f.eq_linearEquivConjAlgEquiv
  refine ⟨LinearMap.toMatrix' T.toLinearMap, LinearMap.toMatrix' T.symm.toLinearMap, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · intro X
    have h1 : Matrix.toLinAlgEquiv' (φ X) = f (Matrix.toLinAlgEquiv' X) := by
      simp [f]
    rw [hT, LinearEquiv.conjAlgEquiv_apply] at h1
    have h2 := congrArg LinearMap.toMatrix' h1
    rw [show (Matrix.toLinAlgEquiv' (φ X) : (Fin 2 → F) →ₗ[F] Fin 2 → F) = Matrix.toLin' (φ X)
      from rfl, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_comp,
      LinearMap.toMatrix'_comp] at h2
    rw [h2, show LinearMap.toMatrix' (Matrix.toLinAlgEquiv' X) = X from
      LinearMap.toMatrix'_toLin' X, Matrix.mul_assoc]

theorem exists_eq_mul_mul (y : Matrix (Fin 2) (Fin 2) F ≃ₗ[F] Matrix (Fin 2) (Fin 2) F)
    (hy : ∀ g : SL(2, F), ∃ g' : SL(2, F), ∀ X,
      y ((g : Matrix (Fin 2) (Fin 2) F) * X) = (g' : Matrix _ _ F) * y X) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) F, IsUnit P.det ∧ IsUnit Q.det ∧ ∀ X, y X = P * X * Q := by
  classical
  choose g' hg' using hy
  set Y₀ := y 1 with hY₀
  have hyg : ∀ g : SL(2, F), y (g : Matrix (Fin 2) (Fin 2) F) = (g' g : Matrix _ _ F) * Y₀ := by
    intro g
    have := hg' g 1
    rwa [mul_one] at this
  obtain ⟨X₁, hX₁⟩ := y.surjective 1
  obtain ⟨gs, hgs⟩ := exists_sl_sum X₁
  have hleft : (∑ i, (g' (gs i) : Matrix (Fin 2) (Fin 2) F)) * Y₀ = 1 := by
    rw [← hX₁, hgs, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (hyg (gs i)).symm
  have hdetY : IsUnit Y₀.det := by
    have := congrArg Matrix.det hleft
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one_right _ this
  set Yinv := Y₀⁻¹ with hYinv
  have hYY : Y₀ * Yinv = 1 := Matrix.mul_nonsing_inv Y₀ hdetY
  have hYY' : Yinv * Y₀ = 1 := Matrix.nonsing_inv_mul Y₀ hdetY
  let φl : Matrix (Fin 2) (Fin 2) F ≃ₗ[F] Matrix (Fin 2) (Fin 2) F :=
    y.trans
      { toFun := fun X => X * Yinv
        invFun := fun X => X * Y₀
        map_add' := fun X Z => Matrix.add_mul X Z Yinv
        map_smul' := fun c X => Matrix.smul_mul c X Yinv
        left_inv := fun X => by simp [Matrix.mul_assoc, hYY']
        right_inv := fun X => by simp [Matrix.mul_assoc, hYY] }
  have hφl : ∀ X, φl X = y X * Yinv := fun X => rfl
  have hφg : ∀ (g : SL(2, F)) Z, φl ((g : Matrix (Fin 2) (Fin 2) F) * Z) =
      φl (g : Matrix (Fin 2) (Fin 2) F) * φl Z := by
    intro g Z
    rw [hφl, hφl, hφl, hg', hyg, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc Y₀ Yinv, hYY, Matrix.one_mul]
  have hmul : ∀ X Z, φl (X * Z) = φl X * φl Z := by
    intro X Z
    obtain ⟨hs, rfl⟩ := exists_sl_sum X
    rw [Finset.sum_mul, map_sum, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => hφg (hs i) Z
  have hone : φl 1 = 1 := by rw [hφl, ← hY₀, hYY]
  obtain ⟨P, Pinv, hPP, hPP', hP⟩ := exists_inner_of_algEquiv (AlgEquiv.ofLinearEquiv φl hone hmul)
  refine ⟨P, Pinv * Y₀, ?_, ?_, fun X => ?_⟩
  · have := congrArg Matrix.det hPP
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ this
  · rw [Matrix.det_mul]
    have := congrArg Matrix.det hPP'
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact (IsUnit.of_mul_eq_one _ this).mul hdetY
  · have h1 := hP X
    rw [AlgEquiv.ofLinearEquiv_apply, hφl] at h1
    calc y X = y X * Yinv * Y₀ := by rw [Matrix.mul_assoc, hYY', Matrix.mul_one]
      _ = P * X * (Pinv * Y₀) := by rw [h1]; simp [Matrix.mul_assoc]

end CFSG.Quasithin.H13.L14324
