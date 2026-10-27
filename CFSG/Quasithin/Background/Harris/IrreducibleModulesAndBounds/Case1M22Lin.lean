module

public import CFSG.CharacterTheory.SteinbergBYModularRealization
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.CharacterTheory.SteinbergBY Matrix

theorem trace_symm_eq_of_invariant {K N : Type*} [Field K] [AddCommGroup N] [Module K N]
    [Module.Finite K N] (B : LinearMap.BilinForm K N) (hB : B.Nondegenerate) (T : N ≃ₗ[K] N)
    (hT : ∀ x y, B (T x) (T y) = B x y) :
    LinearMap.trace K N (T.symm : N →ₗ[K] N) = LinearMap.trace K N (T : N →ₗ[K] N) := by
  classical
  let b := Module.finBasis K N
  set G := LinearMap.BilinForm.toMatrix b B with hG
  set M := LinearMap.toMatrix b b (T : N →ₗ[K] N) with hM
  set M' := LinearMap.toMatrix b b (T.symm : N →ₗ[K] N) with hM'
  have hdet : G.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hB
  have hunit : IsUnit G.det := Ne.isUnit hdet
  have h1 : M * M' = 1 := by
    rw [hM, hM', ← LinearMap.toMatrix_mul]
    have : (T : N →ₗ[K] N) * (T.symm : N →ₗ[K] N) = 1 := by
      ext x
      simp
    rw [this, LinearMap.toMatrix_one]
  have h2 : Mᵀ * G * M = G := by
    have := LinearMap.BilinForm.toMatrix_comp b b B (T : N →ₗ[K] N) (T : N →ₗ[K] N)
    rw [← hG, ← hM] at this
    rw [← this]
    congr 1
    ext x y
    exact hT x y
  have h3 : Mᵀ * G = G * M' := by
    calc Mᵀ * G = Mᵀ * G * (M * M') := by rw [h1, Matrix.mul_one]
      _ = (Mᵀ * G * M) * M' := by simp only [Matrix.mul_assoc]
      _ = G * M' := by rw [h2]
  have h4 : M' = G⁻¹ * (Mᵀ * G) := by
    rw [h3, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hunit, Matrix.one_mul]
  rw [LinearMap.trace_eq_matrix_trace K b, LinearMap.trace_eq_matrix_trace K b, ← hM, ← hM', h4,
    Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv G hunit, Matrix.mul_one,
    Matrix.trace_transpose]

theorem matrix_scalar_of_commute {G : Type} [Group G] {n : ℕ} [NeZero n]
    (M : G →* Matrix (Fin n) (Fin n) (ZMod 2))
    (hirr : (matrixBaseChange (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))) M).IsIrreducible)
    (T : Matrix (Fin n) (Fin n) (ZMod 2)) (hT : ∀ g, T * M g = M g * T) :
    ∃ c : ZMod 2, T = c • (1 : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  classical
  let k := AlgebraicClosure (ZMod 2)
  let ψ : ZMod 2 →+* k := algebraMap (ZMod 2) k
  let f := intertwiningMapOfMatrix ψ M M T hT
  have hb := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := matrixBaseChange ψ M)
  obtain ⟨c, hc⟩ := hb.2 f
  have key : ∀ i j, ψ (T i j) = if i = j then c else 0 := by
    intro i j
    have h := congrArg
      (fun F : (matrixBaseChange ψ M).IntertwiningMap (matrixBaseChange ψ M) =>
        F.toLinearMap (Pi.single j 1) i) hc
    simp [f, intertwiningMapOfMatrix] at h
    rw [← h, Pi.single_apply]
    split_ifs <;> simp
  have hinj : Function.Injective ψ := ψ.injective
  let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  refine ⟨T i0 i0, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    apply hinj
    have h1 := key i i
    have h0 := key i0 i0
    simp only [ite_true] at h1 h0
    simp [h1, h0]
  · apply hinj
    have h1 := key i j
    simp only [hij, ite_false] at h1
    simp [h1, hij]

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
