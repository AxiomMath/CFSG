module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open Matrix

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg

variable {K : Type*} [Field K]

@[expose] def aMat (ω : K) : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![1, ω, ω ^ 2]

@[expose] def bMat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem aMat_eq (ω : K) : aMat ω = !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aMat]

theorem aMat_mul_bMat {ω : K} (hω : ω ^ 3 = 1) : aMat ω * bMat = ω • (bMat * aMat ω) := by
  rw [aMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bMat, Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination -hω
  · ring

theorem aMat_pow_three {ω : K} (hω : ω ^ 3 = 1) : aMat ω ^ 3 = 1 := by
  rw [aMat_eq, pow_succ, pow_succ, pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination hω
  · linear_combination (ω ^ 3 + 1) * hω

theorem bMat_pow_three : (bMat : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  rw [pow_succ, pow_succ, pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_aMat {ω : K} (hω : ω ^ 3 = 1) : (aMat ω).det = 1 := by
  simp [aMat, Matrix.det_diagonal, Fin.prod_univ_three]
  linear_combination hω

theorem det_bMat : (bMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [bMat, Matrix.det_fin_three]

theorem aMat_unitary (σ : K →+* K) {ω : K} (hω : σ ω * ω = 1) :
    ((aMat ω).map σ)ᵀ * aMat ω = 1 := by
  rw [aMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · exact hω
  · linear_combination (σ ω * ω + 1) * hω

theorem bMat_unitary (σ : K →+* K) :
    ((bMat : Matrix (Fin 3) (Fin 3) K).map σ)ᵀ * bMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem ne_zero_of_pow_three {ω : K} (hω : ω ^ 3 = 1) : ω ≠ 0 := by
  rintro rfl; norm_num at hω

theorem sq_ne_one_of_pow_three {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) : ω ^ 2 ≠ 1 := by
  intro h
  apply hω1
  have h0 := ne_zero_of_pow_three hω
  have : ω = ω ^ 3 / ω ^ 2 := by field_simp
  rw [this, hω, h]; simp

theorem sq_ne_self_of_pow_three {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) : ω ^ 2 ≠ ω := by
  intro h
  apply hω1
  have h0 := ne_zero_of_pow_three hω
  have : ω * (ω - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' h0
  · linear_combination h'

theorem diag_of_commute {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) {X : Matrix (Fin 3) (Fin 3) K}
    (ha : X * aMat ω = aMat ω * X) : ∀ i j, i ≠ j → X i j = 0 := by
  have h21 := sq_ne_one_of_pow_three hω hω1
  have hωω := sq_ne_self_of_pow_three hω hω1
  have e : ∀ i j, X i j * (aMat ω) j j = (aMat ω) i i * X i j := by
    intro i j
    have := congrFun (congrFun ha i) j
    simpa [aMat, Matrix.mul_apply, Matrix.diagonal_apply] using this
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  simp [aMat] at e01 e02 e10 e12 e20 e21
  have z01 : X 0 1 = 0 := by
    by_contra h; exact hω1 (mul_left_cancel₀ h (by linear_combination e01))
  have z02 : X 0 2 = 0 := by
    by_contra h; exact h21 (mul_left_cancel₀ h (by linear_combination e02))
  have z10 : X 1 0 = 0 := by
    by_contra h; exact hω1 (mul_left_cancel₀ h (by linear_combination -e10))
  have z12 : X 1 2 = 0 := by
    by_contra h; exact hωω (mul_left_cancel₀ h (by linear_combination e12))
  have z20 : X 2 0 = 0 := by
    by_contra h; exact h21 (mul_left_cancel₀ h (by linear_combination -e20))
  have z21 : X 2 1 = 0 := by
    by_contra h; exact hωω (mul_left_cancel₀ h (by linear_combination -e21))
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem circulant_of_commute {Y : Matrix (Fin 3) (Fin 3) K} (hb : Y * bMat = bMat * Y) :
    Y = !![Y 0 0, Y 0 1, Y 0 2; Y 0 2, Y 0 0, Y 0 1; Y 0 1, Y 0 2, Y 0 0] := by
  have b10 := congrFun (congrFun hb 1) 0
  have b11 := congrFun (congrFun hb 1) 1
  have b12 := congrFun (congrFun hb 1) 2
  have b20 := congrFun (congrFun hb 2) 0
  have b21 := congrFun (congrFun hb 2) 1
  have b22 := congrFun (congrFun hb 2) 2
  simp [bMat, Matrix.mul_apply, Fin.sum_univ_three] at b10 b11 b12 b20 b21 b22
  ext i j
  fin_cases i <;> fin_cases j <;> simp [b10, b11, b12, b20, b21, b22]

theorem commutant {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) {X : Matrix (Fin 3) (Fin 3) K}
    (ha : X * aMat ω = aMat ω * X) (hb : X * bMat = bMat * X) : ∃ c : K, X = c • 1 := by
  have hd := diag_of_commute hω hω1 ha
  have hX := circulant_of_commute hb
  refine ⟨X 0 0, ?_⟩
  rw [hX, hd 0 1 (by decide), hd 0 2 (by decide)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem scalar_of_commute_diag_circulant {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {X Y : Matrix (Fin 3) (Fin 3) K} (ha : X * aMat ω = aMat ω * X)
    (hb : Y * bMat = bMat * Y) (hXY : X * Y = Y * X) (hX : ∀ c : K, X ≠ c • 1) :
    ∃ c : K, Y = c • 1 := by
  have hd := diag_of_commute hω hω1 ha
  have hY := circulant_of_commute hb
  have e : ∀ i j, X i i * Y i j = Y i j * X j j := by
    intro i j
    have h1 : (X * Y) i j = X i i * Y i j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · intro k _ hk; rw [hd i k (Ne.symm hk)]; simp
      · simp
    have h2 : (Y * X) i j = Y i j * X j j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · intro k _ hk; rw [hd k j hk]; simp
      · simp
    rw [← h1, ← h2, hXY]
  have hscal : X 0 0 = X 1 1 → X 1 1 = X 2 2 → False := by
    intro h1 h2
    apply hX (X 0 0)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd, h1, h2]
  have y1 : Y 0 1 = 0 := by
    by_contra h
    have h01 := e 0 1
    have h12 := e 1 2
    have h20 := e 2 0
    rw [hY] at h01 h12 h20
    simp at h01 h12 h20
    exact hscal (mul_left_cancel₀ h (by linear_combination h01))
      (mul_left_cancel₀ h (by linear_combination h12))
  have y2 : Y 0 2 = 0 := by
    by_contra h
    have h02 := e 0 2
    have h10 := e 1 0
    have h21 := e 2 1
    rw [hY] at h02 h10 h21
    simp at h02 h10 h21
    exact hscal (mul_left_cancel₀ h (by linear_combination -h10))
      (mul_left_cancel₀ h (by linear_combination -h21))
  refine ⟨Y 0 0, ?_⟩
  rw [hY, y1, y2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg
