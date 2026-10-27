module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
public import CFSG.LocalAnalysis.ComponentInitial.LinearOrthogonalBasis
public import Mathlib.Algebra.Field.ZMod
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
public import CFSG.LieType.Universal.SpinOmega.Range

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal

set_option backward.isDefEq.respectTransparency false

scoped instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

@[expose] def fiveWeight (k : ℕ) (ε : Bool) : Fin (k + 1) → ZMod 5 :=
  fun i => if i = Fin.last k then -(if ε then 1 else 2) else 1

@[expose] noncomputable def fiveQ (k : ℕ) (ε : Bool) :
    QuadraticForm (ZMod 5) (Fin (k + 1) → ZMod 5) :=
  QuadraticMap.weightedSumSquares (ZMod 5) (fiveWeight k ε)

theorem fiveWeight_castSucc (k : ℕ) (ε : Bool) (i : Fin k) :
    fiveWeight k ε i.castSucc = 1 := by
  simp only [fiveWeight, if_neg (Fin.castSucc_ne_last i)]

theorem fiveWeight_last (k : ℕ) (ε : Bool) :
    fiveWeight k ε (Fin.last k) = -(if ε then 1 else 2) := by
  simp [fiveWeight]

theorem fiveQ_apply (k : ℕ) (ε : Bool) (x : Fin (k + 1) → ZMod 5) :
    fiveQ k ε x = fiveForm k ε x x := by
  rw [fiveQ, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_castSucc, fiveForm]
  simp only [fiveWeight_castSucc, fiveWeight_last, smul_eq_mul, one_mul]
  ring

theorem fiveQ_polar (k : ℕ) (ε : Bool) (x y : Fin (k + 1) → ZMod 5) :
    polar (fiveQ k ε) x y = 2 * fiveForm k ε x y := by
  rw [QuadraticMap.polar, fiveQ_apply, fiveQ_apply, fiveQ_apply]
  simp only [fiveForm, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  rw [show (∑ x_1 : Fin k, y x_1.castSucc * x x_1.castSucc) =
      ∑ x_1 : Fin k, x x_1.castSucc * y x_1.castSucc from
    Finset.sum_congr rfl fun i _ => mul_comm _ _]
  ring

theorem fiveQ_nondegenerate (k : ℕ) (ε : Bool) : (fiveQ k ε).Nondegenerate := by
  letI : Invertible (2 : ZMod 5) :=
    invertibleOfNonzero (show (2 : ZMod 5) ≠ 0 by decide)
  rw [fiveQ]
  refine QuadraticMap.nondegenerate_weightedSumSquares (w := fiveWeight k ε) fun i => ?_
  exact isRegular_iff_ne_zero.mpr (by
    simp only [fiveWeight]
    split_ifs <;> decide)

@[expose] noncomputable def fiveGLIso (k : ℕ) :
    GL (Fin (k + 1)) (ZMod 5) ≃*
      ((Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem fiveGLIso_apply (k : ℕ) (g : GL (Fin (k + 1)) (ZMod 5))
    (x : Fin (k + 1) → ZMod 5) :
    fiveGLIso k g x = (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x := by
  simp [fiveGLIso, Matrix.GeneralLinearGroup.toLin]

@[expose] noncomputable def fiveReflO (k : ℕ) (ε : Bool) (v : Fin (k + 1) → ZMod 5) :
    (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5) :=
  @reflect (ZMod 5) (Fin (k + 1) → ZMod 5) _ _ _ (fiveQ k ε) v

theorem fiveGLIso_fiveReflOf (k : ℕ) (ε : Bool) (v : Fin (k + 1) → ZMod 5) :
    fiveGLIso k (fiveReflOf k ε v) = fiveReflO k ε v := by
  apply LinearEquiv.ext
  intro x
  rw [fiveReflO, fiveGLIso_apply, fiveReflOf_mulVec]
  by_cases hv : fiveForm k ε v v = 0
  · rw [hv, _root_.inv_zero, mul_zero, zero_smul, sub_zero]
    exact (congrArg (fun e => e x)
      (reflect_of_map_eq_zero (K := ZMod 5) (V := Fin (k + 1) → ZMod 5)
        (Q := fiveQ k ε) (by rw [fiveQ_apply]; exact hv))).symm
  · rw [reflect_apply (K := ZMod 5) (V := Fin (k + 1) → ZMod 5) (Q := fiveQ k ε)
      (by rwa [fiveQ_apply])]
    rw [fiveQ_polar, fiveQ_apply, fiveForm_comm k ε v x, div_eq_mul_inv]

end CFSG.OddTranspositions.PartThree
