module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LieType.RootSystem.Form
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open scoped Matrix

inductive LevTwoType : Type
  | A (n : ℕ) | B (n : ℕ) | D (n : ℕ) | E6 | E7 | E8 | F4

namespace LevTwoType

@[expose] def n : LevTwoType → ℕ
  | A n => n | B n => n | D n => n | E6 => 6 | E7 => 7 | E8 => 8 | F4 => 4

@[expose] def pair : (T : LevTwoType) → Matrix (Fin T.n) (Fin T.n) ℤ
  | A n => CartanMatrix.A n
  | B n => CartanMatrix.B n
  | D n => CartanMatrix.D n
  | E6 => CartanMatrix.E 6
  | E7 => CartanMatrix.E 7
  | E8 => CartanMatrix.E 8
  | F4 => CartanMatrix.F₄

@[expose] def coxeter : (T : LevTwoType) → CoxeterMatrix (Fin T.n)
  | A n => CoxeterMatrix.A n
  | B n => CoxeterMatrix.B n
  | D n => ggCoxeterMatrixD n
  | E6 => CoxeterMatrix.E₆
  | E7 => CoxeterMatrix.E₇
  | E8 => CoxeterMatrix.E₈
  | F4 => CoxeterMatrix.F₄

@[expose] def Valid : LevTwoType → Prop
  | A n => 1 ≤ n
  | B n => 2 ≤ n
  | D n => 4 ≤ n
  | _ => True

@[expose] def root (T : LevTwoType) : Matrix (Fin T.n) (Fin T.n) ℤ := (T.pair)ᵀ

theorem pairFT : ∀ T : LevTwoType, TauCeti.IsFiniteType T.pair
  | A n => TauCeti.isFiniteType_cartanMatrix_A n
  | B n => TauCeti.isFiniteType_cartanMatrix_B n
  | D n => TauCeti.isFiniteType_cartanMatrix_D n
  | E6 => by
      have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E6
      rw [TauCeti.DynkinType.cartanMatrix_E6] at h
      exact h
  | E7 => by
      have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E7
      rw [TauCeti.DynkinType.cartanMatrix_E7] at h
      exact h
  | E8 => by
      have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E8
      rw [TauCeti.DynkinType.cartanMatrix_E8] at h
      exact h
  | F4 => by
      have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_F4
      rw [TauCeti.DynkinType.cartanMatrix_F4] at h
      exact h

theorem rootFT (T : LevTwoType) : TauCeti.IsFiniteType T.root := (pairFT T).transpose

end LevTwoType

end CFSG.StandardType.LevTwo
