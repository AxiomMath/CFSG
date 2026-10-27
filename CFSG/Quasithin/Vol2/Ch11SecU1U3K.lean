module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem eq_one_of_mul_eq_smul {n : Type*} [Fintype n] [DecidableEq n] {X Xi U : Matrix n n K}
    {ζ : K} (hX : Xi * X = 1) (h : X * U = ζ • (U * X)) (htr : U.trace ≠ 0) : ζ = 1 := by
  have hX' : X * Xi = 1 := mul_eq_one_comm.mp hX
  have h1 : (X * U * Xi).trace = U.trace := by
    rw [Matrix.trace_mul_cycle, hX, Matrix.one_mul]
  rw [h, Matrix.smul_mul, Matrix.trace_smul, Matrix.mul_assoc, hX', Matrix.mul_one,
    smul_eq_mul] at h1
  have h2 : (ζ - 1) * U.trace = 0 := by linear_combination h1
  linear_combination (mul_eq_zero.mp h2).resolve_right htr

variable {p : ℕ}

theorem hypProj_eq_one_of_scalar (h : UnitaryFieldData p 1 K) {X : hypSU h 1 1} {ℓ : K}
    (hX : ((X : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      Matrix.scalar (HypIndex 1 1) ℓ) : hypProj h 1 1 X = 1 := by
  obtain ⟨hu, hdet⟩ := mem_hypSU.mp X.2
  rw [hX] at hu hdet
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    card_hypIndex] at hdet
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hdet
    exact zero_ne_one hdet
  have h1 : ((Matrix.scalar (HypIndex 1 1) ℓ).map h.bar)ᵀ * hypGram 1 1 K *
      Matrix.scalar (HypIndex 1 1) ℓ = (h.bar ℓ * ℓ) • hypGram 1 1 K := by
    rw [Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [h1] at hu
  have h2 := congrArg (· * hypGram 1 1 K) hu
  simp only [Matrix.smul_mul, hypGram_mul_self] at h2
  have hN : h.bar ℓ * ℓ = 1 := by
    have h3 := congrFun (congrFun h2 (Sum.inl 0)) (Sum.inl 0)
    simpa using h3
  rw [← MonoidHom.mem_ker, ker_hypProj]
  refine ⟨Units.mk0 ℓ hℓ0, ?_, ?_, ?_⟩
  · rw [Units.val_mk0, UnitaryFieldData.norm, mul_comm]
    exact hN
  · exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]; exact hdet)
  · exact Units.ext (by rw [hX, GeneralLinearGroup.coe_scalar, Units.val_mk0])

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
