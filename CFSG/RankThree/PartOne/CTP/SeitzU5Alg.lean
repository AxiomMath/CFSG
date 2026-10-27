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
public import Mathlib.RingTheory.Radical.NatInt
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

public section

namespace CFSG.RankThree.PartOne.CTP.U5Alg

open Matrix

section Algebra

variable {R : Type*} [CommRing R]

@[expose] def A5 (s p r t m : R) : Matrix (Fin 5) (Fin 5) R :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 0 then s else p)
    else if j = 0 then r else (if i = j then t else 0) + m

theorem A5_mul (h2 : (2 : R) = 0) (s p r t m s' p' r' t' m' : R) :
    A5 s p r t m * A5 s' p' r' t' m' =
      A5 (s * s') (s * p' + p * t') (r * s' + t * r') (t * t') (r * p' + t * m' + m * t') := by
  have h4 : (4 : R) = 0 := by
    have : (4 : R) = 2 * 2 := by norm_num
    rw [this, h2, zero_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A5, Matrix.mul_apply, Fin.sum_univ_five] <;>
    first
      | rfl
      | linear_combination (p * r') * h4
      | linear_combination (p * m') * h4
      | linear_combination (m * r') * h4
      | linear_combination (m * m') * h4

theorem A5_map_transpose {S : Type*} [CommRing S] (φ : R →+* S) (s p r t m : R) :
    ((A5 s p r t m).map φ)ᵀ = A5 (φ s) (φ r) (φ p) (φ t) (φ m) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A5]

theorem A5_one : A5 (1 : R) 0 0 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A5]

@[expose] def U5 (p r m : R) : Matrix (Fin 5) (Fin 5) R := A5 1 p r 1 m

theorem U5_mul (h2 : (2 : R) = 0) (p r m p' r' m' : R) :
    U5 p r m * U5 p' r' m' = U5 (p + p') (r + r') (m + m' + r * p') := by
  rw [U5, U5, U5, A5_mul h2]
  congr 1 <;> ring

theorem U5_comm (h2 : (2 : R) = 0) (p r m p' r' m' : R) :
    U5 p r m * U5 p' r' m' = U5 0 0 (r * p' + r' * p) * (U5 p' r' m' * U5 p r m) := by
  rw [U5_mul h2, U5_mul h2, U5_mul h2]
  congr 1
  · ring
  · ring
  · linear_combination (-(r' * p)) * h2

end Algebra

section Field

variable {F : Type*} [Field F]

@[expose] def hMat (γ : F) : Matrix (Fin 5) (Fin 5) F := A5 ((γ ^ 4)⁻¹) 0 0 γ 0

@[expose] def kMat (η ρ : F) : Matrix (Fin 5) (Fin 5) F :=
  A5 (η * ρ) (η * (ρ + 1)) (η * (ρ + 1)) η (η * (ρ + 1))

theorem hMat_eq_diagonal (γ : F) :
    hMat γ = Matrix.diagonal ![(γ ^ 4)⁻¹, γ, γ, γ, γ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hMat, A5]

theorem kMat_eq_smul (h2 : (2 : F) = 0) (η ρ : F) :
    kMat η ρ = η • (1 + (ρ + 1) • vecMulVec (fun _ : Fin 5 => (1 : F)) (fun _ => 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kMat, A5, vecMulVec] <;>
    first | ring1 | (left; linear_combination (-1) * h2)

theorem kMat_det (h2 : (2 : F) = 0) (η ρ : F) : (kMat η ρ).det = η ^ 5 * ρ := by
  rw [kMat_eq_smul h2, Matrix.det_smul, ← Matrix.vecMulVec_smul, Matrix.vecMulVec_eq (Fin 1),
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [Fintype.card_fin, dotProduct, smul_eq_mul, Pi.smul_apply, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  linear_combination (η ^ 5 * (2 * ρ + 3)) * h2

theorem kMat_conjTr_mul (h2 : (2 : F) = 0) (σ : F →+* F) {η ρ : F} (hη : σ η * η = 1)
    (hρ : σ ρ * ρ = 1) : ((kMat η ρ).map σ)ᵀ * kMat η ρ = 1 := by
  rw [kMat, A5_map_transpose, A5_mul h2, ← A5_one]
  congr 1
  all_goals simp only [map_mul, map_add, map_one]
  · linear_combination (σ ρ * ρ) * hη + hρ
  · linear_combination (σ ρ * ρ + 2 * σ ρ + 1) * hη + hρ + (σ ρ + 1) * h2
  · linear_combination (σ ρ * ρ + 2 * ρ + 1) * hη + hρ + (ρ + 1) * h2
  · linear_combination (σ ρ * ρ + 2 * σ ρ + 2 * ρ + 3) * hη + hρ + (σ ρ + ρ + 2) * h2

theorem hMat_mul_kMat (h2 : (2 : F) = 0) {γ η ρ : F} (hγ : γ ≠ 0) (hη : η ≠ 0) (hρ : ρ ≠ 0) :
    hMat γ * kMat η ρ =
      U5 ((ρ + 1) * ((γ ^ 5)⁻¹ + 1)) (ρ⁻¹ * (ρ + 1) * (γ ^ 5 + 1))
        ((ρ + ρ⁻¹) * (γ ^ 5 + 1)) * (kMat η ρ * hMat γ) := by
  rw [hMat, kMat, U5, A5_mul h2, A5_mul h2, A5_mul h2]
  congr 1
  all_goals field_simp
  · linear_combination (-(γ ^ 5 * (ρ + 1))) * h2
  · linear_combination (-(ρ + 1)) * h2
  · linear_combination (-(γ * (γ ^ 5 + 1) * (ρ ^ 2 + ρ + 1))) * h2

end Field

end CFSG.RankThree.PartOne.CTP.U5Alg
