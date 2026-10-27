
module

public import CFSG.Sporadic.McL.VecSpec
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.Suz.Certificate

public section

namespace CFSG.Sporadic.Suz

open CFSG.F3.Native Native Matrix CFSG.Sporadic.VecOrbit

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev mA : Matrix (Fin 64) (Fin 64) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 64 1 Blueprint.NativeSporadic.SuzSeed1

noncomputable abbrev mB : Matrix (Fin 64) (Fin 64) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 64 1 Blueprint.NativeSporadic.SuzSeed2

private theorem seedA_eq' : seedA = Blueprint.NativeSporadic.SuzSeed1 := rfl

private theorem seedB_eq' : seedB = Blueprint.NativeSporadic.SuzSeed2 := rfl

theorem seedA_eq : seedA = Blueprint.NativeSporadic.SuzSeed1 := seedA_eq'

theorem seedB_eq : seedB = Blueprint.NativeSporadic.SuzSeed2 := seedB_eq'

theorem toMat_matA : toMat 64 matA = mA := by
  unfold matA; rw [toMat_rowsOf, seedA_eq]

theorem toMat_matB : toMat 64 matB = mB := by
  unfold matB; rw [toMat_rowsOf, seedB_eq]

theorem matA_size : matA.size = 64 := by unfold matA rowsOf; simp

theorem matB_size : matB.size = 64 := by unfold matB rowsOf; simp

theorem rowsWF_matA : RowsWF matA := RowsWF.rowsOf 64 seedA

theorem rowsWF_matB : RowsWF matB := RowsWF.rowsOf 64 seedB

structure MatrixFacts : Prop where
  A_sq : mA * mA = 1
  B_cube : mB ^ 3 = 1
  AB_pow : (mA * mB) ^ 13 = 1
  A_ne : mA ≠ 1
  B_ne : mB ≠ 1
  AB_ne : mA * mB ≠ 1

theorem matrixFacts_of (h : matrixChecks = true) : MatrixFacts := by
  unfold matrixChecks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hAc, hBc⟩, hIc⟩, hABc⟩, hA2⟩, hB3⟩, hAB13⟩, hA1⟩, hB1⟩, hAB1⟩ := h
  have hAB_size : (mul 64 matA matB).size = 64 := by rw [mul_size, matA_size]
  have hABwf : RowsWF (mul 64 matA matB) := RowsWF.mul _ 64 rowsWF_matA rowsWF_matB
  have htAB : toMat 64 (mul 64 matA matB) = mA * mB := by
    rw [toMat_mul matA_size rowsWF_matA rowsWF_matB, toMat_matA, toMat_matB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := toMat_eq_of_eqM hA2
    rwa [toMat_mul matA_size rowsWF_matA rowsWF_matA, toMat_idM, toMat_matA] at this
  · have := toMat_eq_of_eqM hB3
    rwa [toMat_powM rowsWF_matB, toMat_idM, toMat_matB] at this
  · have := toMat_eq_of_eqM hAB13
    rwa [toMat_powM hABwf, toMat_idM, htAB] at this
  · have := not_eqM_of_ne matA_size hA1 hAc hIc
    rwa [toMat_idM, toMat_matA] at this
  · have := not_eqM_of_ne matB_size hB1 hBc hIc
    rwa [toMat_idM, toMat_matB] at this
  · have := not_eqM_of_ne hAB_size hAB1 hABc hIc
    rwa [toMat_idM, htAB] at this

private theorem zmod3_pow3_eq_one : ∀ x : ZMod 3, x ^ 3 = 1 → x = 1 := by decide

private theorem zmod3_pow13_eq_one : ∀ x : ZMod 3, x ^ 13 = 1 → x = 1 := by decide

section Facts

variable (hM : MatrixFacts)
include hM

theorem det_mB : mB.det = 1 := by
  apply zmod3_pow3_eq_one
  rw [← Matrix.det_pow, hM.B_cube, Matrix.det_one]

theorem det_mA : mA.det = 1 := by
  have h : (mA * mB).det = 1 := by
    apply zmod3_pow13_eq_one
    rw [← Matrix.det_pow, hM.AB_pow, Matrix.det_one]
  rwa [Matrix.det_mul, det_mB hM, mul_one] at h

theorem det_mA_ne_zero : mA.det ≠ 0 := by rw [det_mA hM]; exact one_ne_zero

theorem det_mB_ne_zero : mB.det ≠ 0 := by rw [det_mB hM]; exact one_ne_zero

end Facts

@[expose] noncomputable def orb : WOrbit := orbitData ()

end CFSG.Sporadic.Suz
