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

namespace CFSG.LocalAnalysis

open Matrix

section Signed

variable {R : Type*} [CommRing R]

@[expose] def antiMat (a b c d e f : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, a, b, c; -a, 0, d, e; -b, -d, 0, f; -c, -e, -f, 0]

@[expose] def pfS (M : Matrix (Fin 4) (Fin 4) R) : R :=
  M 0 1 * M 2 3 - M 0 2 * M 1 3 + M 0 3 * M 1 2

@[expose] def sharpS (M : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 4) (Fin 4) R :=
  antiMat (-M 2 3) (M 1 3) (-M 1 2) (-M 0 3) (M 0 2) (-M 0 1)

theorem det_four (A : Matrix (Fin 4) (Fin 4) R) : A.det =
    A 0 0 * (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 - A 1 2 * A 2 1 * A 3 3 +
        A 1 2 * A 2 3 * A 3 1 + A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1) -
      A 0 1 * (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 - A 1 2 * A 2 0 * A 3 3 +
        A 1 2 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0) +
      A 0 2 * (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 - A 1 1 * A 2 0 * A 3 3 +
        A 1 1 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0) -
      A 0 3 * (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 - A 1 1 * A 2 0 * A 3 2 +
        A 1 1 * A 2 2 * A 3 0 + A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_fin_three, Fin.succAbove, Matrix.submatrix]
  ring

theorem pfS_congr (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    pfS (g * antiMat a b c d e f * gᵀ) = g.det * pfS (antiMat a b c d e f) := by
  rw [det_four]
  simp [pfS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem congr_antiMat_apply_self (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) (i : Fin 4) :
    (g * antiMat a b c d e f * gᵀ) i i = 0 := by
  fin_cases i <;> simp [antiMat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem antiMat_mul_sharpS (a b c d e f : R) :
    antiMat a b c d e f * sharpS (antiMat a b c d e f) = pfS (antiMat a b c d e f) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sharpS, antiMat, pfS, Matrix.mul_apply, Fin.sum_univ_four]
    <;> ring

theorem sharpS_mul_antiMat (a b c d e f : R) :
    sharpS (antiMat a b c d e f) * antiMat a b c d e f = pfS (antiMat a b c d e f) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sharpS, antiMat, pfS, Matrix.mul_apply, Fin.sum_univ_four]
    <;> ring

theorem det_antiMat (a b c d e f : R) :
    (antiMat a b c d e f).det = pfS (antiMat a b c d e f) ^ 2 := by
  rw [det_four]
  simp [antiMat, pfS]
  ring

theorem sharpS_congr_apply_0_0 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 0 0 =
      (g.det • sharpS (antiMat a b c d e f)) 0 0 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_0_1 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 0 1 =
      (g.det • sharpS (antiMat a b c d e f)) 0 1 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_0_2 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 0 2 =
      (g.det • sharpS (antiMat a b c d e f)) 0 2 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_0_3 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 0 3 =
      (g.det • sharpS (antiMat a b c d e f)) 0 3 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_1_0 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 1 0 =
      (g.det • sharpS (antiMat a b c d e f)) 1 0 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_1_1 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 1 1 =
      (g.det • sharpS (antiMat a b c d e f)) 1 1 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_1_2 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 1 2 =
      (g.det • sharpS (antiMat a b c d e f)) 1 2 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_1_3 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 1 3 =
      (g.det • sharpS (antiMat a b c d e f)) 1 3 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_2_0 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 2 0 =
      (g.det • sharpS (antiMat a b c d e f)) 2 0 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_2_1 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 2 1 =
      (g.det • sharpS (antiMat a b c d e f)) 2 1 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_2_2 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 2 2 =
      (g.det • sharpS (antiMat a b c d e f)) 2 2 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_2_3 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 2 3 =
      (g.det • sharpS (antiMat a b c d e f)) 2 3 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_3_0 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 3 0 =
      (g.det • sharpS (antiMat a b c d e f)) 3 0 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_3_1 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 3 1 =
      (g.det • sharpS (antiMat a b c d e f)) 3 1 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_3_2 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 3 2 =
      (g.det • sharpS (antiMat a b c d e f)) 3 2 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr_apply_3_3 (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    (gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g) 3 3 =
      (g.det • sharpS (antiMat a b c d e f)) 3 3 := by
  rw [det_four]
  simp [sharpS, antiMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem sharpS_congr (g : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    gᵀ * sharpS (g * antiMat a b c d e f * gᵀ) * g = g.det • sharpS (antiMat a b c d e f) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact sharpS_congr_apply_0_0 g a b c d e f
  · exact sharpS_congr_apply_0_1 g a b c d e f
  · exact sharpS_congr_apply_0_2 g a b c d e f
  · exact sharpS_congr_apply_0_3 g a b c d e f
  · exact sharpS_congr_apply_1_0 g a b c d e f
  · exact sharpS_congr_apply_1_1 g a b c d e f
  · exact sharpS_congr_apply_1_2 g a b c d e f
  · exact sharpS_congr_apply_1_3 g a b c d e f
  · exact sharpS_congr_apply_2_0 g a b c d e f
  · exact sharpS_congr_apply_2_1 g a b c d e f
  · exact sharpS_congr_apply_2_2 g a b c d e f
  · exact sharpS_congr_apply_2_3 g a b c d e f
  · exact sharpS_congr_apply_3_0 g a b c d e f
  · exact sharpS_congr_apply_3_1 g a b c d e f
  · exact sharpS_congr_apply_3_2 g a b c d e f
  · exact sharpS_congr_apply_3_3 g a b c d e f

end Signed

section CharTwo

variable {F : Type*} [Field F]

@[expose] def altMat (a b c d e f : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, a, b, c; a, 0, d, e; b, d, 0, f; c, e, f, 0]

@[expose] def pfaff (X : Matrix (Fin 4) (Fin 4) F) : F :=
  X 0 1 * X 2 3 + X 0 2 * X 1 3 + X 0 3 * X 1 2

@[expose] def sharp (X : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin 4) (Fin 4) F :=
  altMat (X 2 3) (X 1 3) (X 1 2) (X 0 3) (X 0 2) (X 0 1)

@[expose] def IsAltMat (X : Matrix (Fin 4) (Fin 4) F) : Prop :=
  Xᵀ = X ∧ ∀ i, X i i = 0

theorem isAltMat_altMat (a b c d e f : F) : IsAltMat (altMat a b c d e f) := by
  refine ⟨?_, fun i => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [altMat]
  · fin_cases i <;> simp [altMat]

theorem eq_altMat_of_isAltMat {X : Matrix (Fin 4) (Fin 4) F} (hX : IsAltMat X) :
    X = altMat (X 0 1) (X 0 2) (X 0 3) (X 1 2) (X 1 3) (X 2 3) := by
  have hs : ∀ i j, X j i = X i j := fun i j => congrFun (congrFun hX.1 i) j
  ext i j
  fin_cases i <;> fin_cases j <;> simp [altMat, hX.2] <;> exact hs _ _

theorem sharp_add (X Y : Matrix (Fin 4) (Fin 4) F) : sharp (X + Y) = sharp X + sharp Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sharp, altMat]

variable [CharP F 2]

theorem altMat_eq_antiMat (a b c d e f : F) : altMat a b c d e f = antiMat a b c d e f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [altMat, antiMat, CharTwo.neg_eq]

theorem pfaff_eq_pfS (X : Matrix (Fin 4) (Fin 4) F) : pfaff X = pfS X := by
  simp [pfaff, pfS, CharTwo.sub_eq_add]

theorem sharp_eq_sharpS (X : Matrix (Fin 4) (Fin 4) F) : sharp X = sharpS X := by
  simp [sharp, sharpS, altMat_eq_antiMat, CharTwo.neg_eq]

theorem char_two_alternating_four_Pfaffian_identities :
    (∀ a b c d e f : F, IsAltMat (altMat a b c d e f) ∧
      pfaff (altMat a b c d e f) = a * f + b * e + c * d ∧
      sharp (altMat a b c d e f) = altMat f e d c b a) ∧
    (∀ X : Matrix (Fin 4) (Fin 4) F, IsAltMat X →
      X = altMat (X 0 1) (X 0 2) (X 0 3) (X 1 2) (X 1 3) (X 2 3)) ∧
    (∀ X : Matrix (Fin 4) (Fin 4) F, IsAltMat X →
      sharp (sharp X) = X ∧ pfaff (sharp X) = pfaff X ∧
      X * sharp X = pfaff X • (1 : Matrix (Fin 4) (Fin 4) F) ∧
      sharp X * X = pfaff X • (1 : Matrix (Fin 4) (Fin 4) F) ∧ X.det = pfaff X ^ 2) ∧
    (∀ X Y : Matrix (Fin 4) (Fin 4) F, IsAltMat X → IsAltMat Y →
      X * sharp Y + Y * sharp X =
        (pfaff (X + Y) - pfaff X - pfaff Y) • (1 : Matrix (Fin 4) (Fin 4) F)) ∧
    ∀ (g : GeneralLinearGroup (Fin 4) F) (X : Matrix (Fin 4) (Fin 4) F), IsAltMat X →
      IsAltMat ((g : Matrix (Fin 4) (Fin 4) F) * X * (g : Matrix (Fin 4) (Fin 4) F)ᵀ) ∧
      pfaff ((g : Matrix (Fin 4) (Fin 4) F) * X * (g : Matrix (Fin 4) (Fin 4) F)ᵀ) =
        (g : Matrix (Fin 4) (Fin 4) F).det * pfaff X ∧
      sharp ((g : Matrix (Fin 4) (Fin 4) F) * X * (g : Matrix (Fin 4) (Fin 4) F)ᵀ) =
        (g : Matrix (Fin 4) (Fin 4) F).det •
          ((↑(g⁻¹) : Matrix (Fin 4) (Fin 4) F)ᵀ * sharp X *
            (↑(g⁻¹) : Matrix (Fin 4) (Fin 4) F)) := by
  have hanti : ∀ X : Matrix (Fin 4) (Fin 4) F, IsAltMat X →
      X = antiMat (X 0 1) (X 0 2) (X 0 3) (X 1 2) (X 1 3) (X 2 3) := fun X hX =>
    (eq_altMat_of_isAltMat hX).trans (altMat_eq_antiMat _ _ _ _ _ _)
  have hmul : ∀ X : Matrix (Fin 4) (Fin 4) F, IsAltMat X →
      X * sharp X = pfaff X • (1 : Matrix (Fin 4) (Fin 4) F) ∧
      sharp X * X = pfaff X • (1 : Matrix (Fin 4) (Fin 4) F) := by
    intro X hX
    rw [sharp_eq_sharpS, pfaff_eq_pfS, hanti X hX]
    exact ⟨antiMat_mul_sharpS _ _ _ _ _ _, sharpS_mul_antiMat _ _ _ _ _ _⟩
  refine ⟨fun a b c d e f => ⟨isAltMat_altMat a b c d e f, ?_, ?_⟩,
    fun X hX => eq_altMat_of_isAltMat hX, fun X hX => ⟨?_, ?_, (hmul X hX).1, (hmul X hX).2, ?_⟩,
    fun X Y hX hY => ?_, fun g X hX => ⟨?_, ?_, ?_⟩⟩
  · simp only [pfaff, altMat]
    simp
  · simp only [sharp, altMat]
    simp
  · conv_rhs => rw [eq_altMat_of_isAltMat hX]
    simp [sharp, altMat]
  · simp only [pfaff, sharp, altMat]
    simp
    ring
  · rw [pfaff_eq_pfS, hanti X hX, det_antiMat]
  ·
    have hXY : IsAltMat (X + Y) := ⟨by rw [Matrix.transpose_add, hX.1, hY.1], fun i => by
      rw [Matrix.add_apply, hX.2 i, hY.2 i, add_zero]⟩
    have h := (hmul (X + Y) hXY).1
    rw [sharp_add, mul_add, add_mul, add_mul, (hmul X hX).1, (hmul Y hY).1] at h
    rw [sub_smul, sub_smul, ← h]
    abel
  ·
    refine ⟨?_, fun i => ?_⟩
    · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hX.1,
        Matrix.mul_assoc]
    · rw [hanti X hX]
      exact congr_antiMat_apply_self _ _ _ _ _ _ _ i
  · rw [pfaff_eq_pfS, pfaff_eq_pfS, hanti X hX]
    exact pfS_congr _ _ _ _ _ _ _
  ·
    set G := (g : Matrix (Fin 4) (Fin 4) F)
    set Gi := (↑(g⁻¹) : Matrix (Fin 4) (Fin 4) F)
    have h1 := sharpS_congr G (X 0 1) (X 0 2) (X 0 3) (X 1 2) (X 1 3) (X 2 3)
    rw [← hanti X hX] at h1
    have hinvT : Giᵀ * Gᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have hinv : G * Gi = 1 := Units.mul_inv g
    rw [sharp_eq_sharpS, sharp_eq_sharpS]
    calc sharpS (G * X * Gᵀ) = Giᵀ * Gᵀ * sharpS (G * X * Gᵀ) * (G * Gi) := by
          rw [hinvT, hinv, Matrix.one_mul, Matrix.mul_one]
      _ = Giᵀ * (Gᵀ * sharpS (G * X * Gᵀ) * G) * Gi := by
          simp only [Matrix.mul_assoc]
      _ = Giᵀ * (G.det • sharpS X) * Gi := by rw [h1]
      _ = G.det • (Giᵀ * sharpS X * Gi) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]

end CharTwo

end CFSG.LocalAnalysis
