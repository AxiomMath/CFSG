module

public import Mathlib.Tactic.NoncommRing
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartOne.AUTSL

open Matrix

section Gram

theorem gram_rel {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (J G' Pm Pi : Matrix ι ι R) (hPPi : Pm * Pi = 1) (hPiP : Pi * Pm = 1)
    (hG : G'ᵀ * J * G' = J) (d : ι → R) (hd : Pm * G' * Pi = Matrix.diagonal d) :
    Matrix.diagonal d * (Piᵀ * J * Pi) * Matrix.diagonal d = Piᵀ * J * Pi := by
  have hG' : G' = Pi * Matrix.diagonal d * Pm := by
    calc G' = (Pi * Pm) * G' * (Pi * Pm) := by rw [hPiP, one_mul, mul_one]
      _ = Pi * (Pm * G' * Pi) * Pm := by noncomm_ring
      _ = Pi * Matrix.diagonal d * Pm := by rw [hd]
  have h1 : Piᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, hPPi, Matrix.transpose_one]
  rw [hG', Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose] at hG
  calc Matrix.diagonal d * (Piᵀ * J * Pi) * Matrix.diagonal d
      = (Piᵀ * Pmᵀ) * Matrix.diagonal d * (Piᵀ * J * Pi) * Matrix.diagonal d * (Pm * Pi) := by
        rw [h1, hPPi]; noncomm_ring
    _ = Piᵀ * (Pmᵀ * (Matrix.diagonal d * Piᵀ) * J * (Pi * Matrix.diagonal d * Pm)) * Pi := by
        noncomm_ring
    _ = Piᵀ * J * Pi := by rw [hG]

theorem gram_rel_inv {R ι : Type*} [Field R] [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι R)
    (d : ι → Rˣ) (h : Matrix.diagonal (fun i => ((d i : Rˣ) : R)) * Q *
      Matrix.diagonal (fun i => ((d i : Rˣ) : R)) = Q) :
    Q * Matrix.diagonal (fun i => ((d i : Rˣ) : R)) =
      Matrix.diagonal (fun i => (((d i : Rˣ) : R))⁻¹) * Q := by
  have h1 : Matrix.diagonal (fun i => (((d i : Rˣ) : R))⁻¹) *
      Matrix.diagonal (fun i => ((d i : Rˣ) : R)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun i => (((d i : Rˣ) : R))⁻¹ * ((d i : Rˣ) : R)) = fun _ => (1 : R) :=
      funext fun i => inv_mul_cancel₀ (d i).ne_zero
    rw [this]
    exact Matrix.diagonal_one
  calc Q * Matrix.diagonal (fun i => ((d i : Rˣ) : R))
      = (Matrix.diagonal (fun i => (((d i : Rˣ) : R))⁻¹) *
          Matrix.diagonal (fun i => ((d i : Rˣ) : R))) * Q *
        Matrix.diagonal (fun i => ((d i : Rˣ) : R)) := by rw [h1, one_mul]
    _ = Matrix.diagonal (fun i => (((d i : Rˣ) : R))⁻¹) *
        (Matrix.diagonal (fun i => ((d i : Rˣ) : R)) * Q *
          Matrix.diagonal (fun i => ((d i : Rˣ) : R))) := by noncomm_ring
    _ = Matrix.diagonal (fun i => (((d i : Rˣ) : R))⁻¹) * Q := by rw [h]

end Gram

end CFSG.RankThree.PartOne.AUTSL
