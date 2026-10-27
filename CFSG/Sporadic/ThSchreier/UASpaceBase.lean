
module

public import CFSG.Sporadic.ThSchreier.CentralizerDataBase
public import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.CentralizerDataBase
public meta import CFSG.Sporadic.ThSchreier.WordsBase
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.DataBase

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

theorem zmod2_sub_eq_add (x y : ZMod 2) : x - y = x + y := by revert x y; decide

theorem zmod2_neg_eq (x : ZMod 2) : -x = x := by revert x; decide

@[expose] def matD120 : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  Matrix.diagonal fun i => if i.val < 120 then 1 else 0

theorem rowsMatrix_rowsD120 : rowsMatrix rowsD120 = matD120 := by
  ext i j
  rw [rowsMatrix_apply]
  simp only [rowsD120, Array.getElem?_ofFn, Fin.is_lt, ↓reduceDIte, Option.getD_some, matD120,
    Matrix.diagonal_apply]
  split_ifs with h1 h2 h2
  · have := congrFun (congrFun rowsMatrix_idRows i) j
    rw [rowsMatrix_apply, Array.getElem?_eq_getElem (by rw [idRows_size]; exact i.isLt),
      Option.getD_some] at this
    rw [show idRows[i.val]! = idRows[i.val]'(by rw [idRows_size]; exact i.isLt) from by
      simp [getElem!_def, Array.getElem?_eq_getElem (by rw [idRows_size]; exact i.isLt)], this,
      Matrix.one_apply, ite_eq_left h2]
  · have := congrFun (congrFun rowsMatrix_idRows i) j
    rw [rowsMatrix_apply, Array.getElem?_eq_getElem (by rw [idRows_size]; exact i.isLt),
      Option.getD_some] at this
    rw [show idRows[i.val]! = idRows[i.val]'(by rw [idRows_size]; exact i.isLt) from by
      simp [getElem!_def, Array.getElem?_eq_getElem (by rw [idRows_size]; exact i.isLt)], this,
      Matrix.one_apply, ite_eq_right h2]
  · rw [V4.toVec_zero]; rfl
  · rw [V4.toVec_zero]; rfl

noncomputable abbrev matUAP : Matrix (Fin 248) (Fin 248) (ZMod 2) := rowsMatrix rowsUAP

noncomputable abbrev matUAQ : Matrix (Fin 248) (Fin 248) (ZMod 2) := rowsMatrix rowsUAQ

theorem vecMul_matD120_apply (w : Fin 248 → ZMod 2) (k : Fin 248) :
    Matrix.vecMul w matD120 k = if k.val < 120 then w k else 0 := by
  rw [matD120, Matrix.vecMul_diagonal]
  split_ifs <;> simp

@[expose] def rowEquiv : RowV ≃ₗ[ZMod 2] (Fin 248 → ZMod 2) := LinearEquiv.refl (ZMod 2) _

@[expose] def inUAT (T : Array V4) (w : V4) : Bool :=
  let s := frApply T w
  (List.range 248).all fun k => k < 120 || !s.testBit k

@[expose] def inUA (w : V4) : Bool := inUAT (frTable rowsUAQ) w

end CFSG.Sporadic.ThSchreier
