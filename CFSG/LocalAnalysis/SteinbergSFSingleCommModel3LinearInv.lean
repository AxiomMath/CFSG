module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Matrix

theorem model3lin_sub_one_mul_self_eq_zero {F' : Type} [Field F'] [CharP F' 2]
    (M : Matrix (Fin 3) (Fin 3) F') (hM : M * M = 1) :
    (M - 1) * (M - 1) = 0 := by
  have h2 : ∀ X : Matrix (Fin 3) (Fin 3) F', X + X = 0 := fun X => by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  have key : (M - 1) * (M - 1) = M * M - (M + M) + 1 := by
    simp only [sub_mul, mul_sub, mul_one, one_mul]
    abel
  rw [key, hM, h2 M, sub_zero]
  exact h2 1

theorem model3lin_exists_mulVec_ne_zero {K : Type} [Field K] {N : Matrix (Fin 3) (Fin 3) K}
    (hN : N ≠ 0) : ∃ x : Fin 3 → K, N *ᵥ x ≠ 0 := by
  by_contra h
  push Not at h
  apply hN
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h1

theorem model3lin_exists_kernel_vector {K : Type} [Field K] {N : Matrix (Fin 3) (Fin 3) K}
    (hNN : N * N = 0) {y : Fin 3 → K} (hy : y ≠ 0) :
    ∃ z : Fin 3 → K, N *ᵥ z = 0 ∧ ∀ c : K, z ≠ c • y := by
  by_contra H
  push Not at H
  have hrange : LinearMap.range (Matrix.mulVecLin N) ≤ LinearMap.ker (Matrix.mulVecLin N) := by
    rintro _ ⟨v, rfl⟩
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hNN,
      Matrix.zero_mulVec]
  have hker : LinearMap.ker (Matrix.mulVecLin N) ≤ K ∙ y := by
    intro z hz
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz
    obtain ⟨c, rfl⟩ := H z hz
    exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin N)
  have h2 := Submodule.finrank_mono hrange
  have h3 := Submodule.finrank_mono hker
  rw [finrank_span_singleton hy] at h3
  rw [Module.finrank_fin_fun] at h1
  omega

theorem model3lin_det_ne_zero {K : Type} [Field K] {N : Matrix (Fin 3) (Fin 3) K}
    {y z x : Fin 3 → K} (hy : y ≠ 0) (hz : ∀ c : K, z ≠ c • y)
    (hNy : N *ᵥ y = 0) (hNz : N *ᵥ z = 0) (hNx : N *ᵥ x = y) :
    (Matrix.of ![y, z, x]).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have e : ∀ j, v 0 * y j + v 1 * z j + v 2 * x j = 0 := fun j => by
    have h := congrFun hvM j
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using h
  have hw : v 0 • y + v 1 • z + v 2 • x = 0 := by
    funext j
    simpa using e j
  have h2 : v 2 • y = 0 := by
    have h := congrArg (fun w => N *ᵥ w) hw
    simpa [Matrix.mulVec_add, Matrix.mulVec_smul, hNy, hNz, hNx] using h
  have hv2 : v 2 = 0 := (smul_eq_zero.mp h2).resolve_right hy
  rw [hv2, zero_smul, add_zero] at hw
  by_cases hv1 : v 1 = 0
  · rw [hv1, zero_smul, add_zero] at hw
    have hv0 : v 0 = 0 := (smul_eq_zero.mp hw).resolve_right hy
    apply hv
    funext i
    fin_cases i <;> simp [hv0, hv1, hv2]
  · apply hz (-(v 1)⁻¹ * v 0)
    funext j
    have hj : v 0 * y j + v 1 * z j = 0 := by
      simpa using congrFun hw j
    have hinv : (v 1)⁻¹ * v 1 = 1 := inv_mul_cancel₀ hv1
    show z j = -(v 1)⁻¹ * v 0 * y j
    linear_combination (v 1)⁻¹ * hj - z j * hinv

theorem model3lin_det_smul_mid {K : Type} [Field K] (c : K) {y z x : Fin 3 → K} :
    (Matrix.of ![y, c • z, x]).det = c * (Matrix.of ![y, z, x]).det := by
  simp [Matrix.det_fin_three]
  ring

theorem model3lin_mul_of_rel {K : Type} [Field K] {N : Matrix (Fin 3) (Fin 3) K}
    {y z x : Fin 3 → K} (hNy : N *ᵥ y = 0) (hNz : N *ᵥ z = 0) (hNx : N *ᵥ x = y) :
    N * (Matrix.of ![y, z, x]).transpose =
      (Matrix.of ![y, z, x]).transpose * Matrix.single 0 2 (1 : K) := by
  have ey : ∀ i, N i 0 * y 0 + N i 1 * y 1 + N i 2 * y 2 = 0 := fun i => by
    have h := congrFun hNy i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have ez : ∀ i, N i 0 * z 0 + N i 1 * z 1 + N i 2 * z 2 = 0 := fun i => by
    have h := congrFun hNz i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have ex : ∀ i, N i 0 * x 0 + N i 1 * x 1 + N i 2 * x 2 = y i := fun i => by
    have h := congrFun hNx i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  ext i j
  fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
    linear_combination ey i
  · simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
    linear_combination ez i
  · simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
    linear_combination ex i

theorem model3lin_adjugate_mul_of_det {K : Type} [Field K] {B : Matrix (Fin 3) (Fin 3) K}
    (h : B.det = 1) : adjugate B * B = 1 := by
  rw [Matrix.adjugate_mul, h, one_smul]

theorem model3lin_core {K : Type} [Field K] {A : Matrix (Fin 3) (Fin 3) K}
    (hNN : (A - 1) * (A - 1) = 0) {x : Fin 3 → K} (hx : (A - 1) *ᵥ x ≠ 0) :
    ∃ B : Matrix (Fin 3) (Fin 3) K, B.det = 1 ∧ A * B = B * transvection 0 2 (1 : K) := by
  obtain ⟨y, hxy⟩ : ∃ y : Fin 3 → K, (A - 1) *ᵥ x = y := ⟨_, rfl⟩
  have hy : y ≠ 0 := by
    rw [← hxy]
    exact hx
  have hNy : (A - 1) *ᵥ y = 0 := by
    rw [← hxy, Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  obtain ⟨z, hNz, hzy⟩ := model3lin_exists_kernel_vector hNN hy
  have hD : (Matrix.of ![y, z, x]).det ≠ 0 :=
    model3lin_det_ne_zero hy hzy hNy hNz hxy
  obtain ⟨c, hc⟩ : ∃ c : K, c * (Matrix.of ![y, z, x]).det = 1 :=
    ⟨_, inv_mul_cancel₀ hD⟩
  have hNz' : (A - 1) *ᵥ (c • z) = 0 := by
    rw [Matrix.mulVec_smul, hNz, smul_zero]
  have hrel := model3lin_mul_of_rel hNy hNz' hxy
  refine ⟨(Matrix.of ![y, c • z, x]).transpose, ?_, ?_⟩
  · rw [Matrix.det_transpose, model3lin_det_smul_mid]
    exact hc
  · have key : A * (Matrix.of ![y, c • z, x]).transpose =
        (A - 1) * (Matrix.of ![y, c • z, x]).transpose +
          (Matrix.of ![y, c • z, x]).transpose := by
      rw [sub_mul, one_mul, sub_add_cancel]
    rw [key, hrel, Matrix.transvection, mul_add, mul_one, add_comm]

theorem model3_linear_involution_conj {F' : Type} [Field F'] [CharP F' 2]
    (A : SpecialLinearGroup (Fin 3) F') (hA : A * A = 1) :
    ∃ B : SpecialLinearGroup (Fin 3) F',
      ((B⁻¹ * A * B : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') = 1 ∨
      ((B⁻¹ * A * B : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') =
        transvection 0 2 (1 : F') := by
  have hMM : (A : Matrix (Fin 3) (Fin 3) F') * (A : Matrix (Fin 3) (Fin 3) F') = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hA, Matrix.SpecialLinearGroup.coe_one]
  have hNN : ((A : Matrix (Fin 3) (Fin 3) F') - 1) * ((A : Matrix (Fin 3) (Fin 3) F') - 1) = 0 :=
    model3lin_sub_one_mul_self_eq_zero _ hMM
  by_cases hA1 : (A : Matrix (Fin 3) (Fin 3) F') = 1
  · refine ⟨1, Or.inl ?_⟩
    simp only [inv_one, mul_one, one_mul]
    exact hA1
  · obtain ⟨x, hx⟩ := model3lin_exists_mulVec_ne_zero (sub_ne_zero.mpr hA1)
    obtain ⟨B, hdetB, hABrel⟩ := model3lin_core hNN hx
    obtain ⟨B', hB'⟩ : ∃ B' : SpecialLinearGroup (Fin 3) F',
        (B' : Matrix (Fin 3) (Fin 3) F') = B :=
      ⟨Subtype.mk B hdetB, rfl⟩
    refine ⟨B', Or.inr ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, hB', mul_assoc, hABrel, ← mul_assoc,
      model3lin_adjugate_mul_of_det hdetB, one_mul]

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
