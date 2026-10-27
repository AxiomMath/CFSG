
module

public import CFSG.Sporadic.Th.SetupBase
import all CFSG.Sporadic.Th.SetupBase

public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public meta import Certificates.Data.CFSGNative.Th.Certificate
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate1022
public import CFSG.Certificates.Kernel.Th.Gen.Dce
public import CFSG.Certificates.Kernel.Th.Gen.DceStruct
public import CFSG.Certificates.Kernel.Th.Gen.Fwd
public import CFSG.Certificates.Kernel.Th.Gen.Gen
public import CFSG.Certificates.Kernel.Th.Gen.Orders
public import CFSG.Certificates.Kernel.Th.Gen.Sylow2
public import CFSG.Certificates.Kernel.Th.Gen.Sylow3
public import CFSG.Certificates.Kernel.Th.Gen.Sylow5
public import CFSG.Certificates.Kernel.Th.Gen.Sylow7
public import CFSG.Certificates.Kernel.Th.S.HswTC
public import CFSG.Sporadic.Th.KernelInputsBase

public section

namespace CFSG.Sporadic.Th

open Native Matrix

theorem rows_A_sq : eqRows (mulRows (rowsOf seedA) (rowsOf seedA)) idRows = true :=
  Certificates.certificate1022.1

theorem rows_B_cube :
    eqRows (mulRows (mulRows (rowsOf seedB) (rowsOf seedB)) (rowsOf seedB)) idRows = true :=
  Certificates.certificate1022.2.1

theorem rows_A_form :
    eqRows (mulRows (mulRows (transposeRows (rowsOf seedA)) fcRows) (rowsOf seedA)) fcRows =
      true :=
  Certificates.certificate1022.2.2.1

theorem rows_B_form :
    eqRows (mulRows (mulRows (transposeRows (rowsOf seedB)) fcRows) (rowsOf seedB)) fcRows =
      true :=
  Certificates.certificate1022.2.2.2

theorem matA_mul_self : matA * matA = 1 := by
  have h := rowsMatrix_eq_of_eqRows rows_A_sq
  rwa [rowsMatrix_mulRows, rowsMatrix_idRows, rowsMatrix_rowsOf_seedA] at h

theorem matB_cube : matB * matB * matB = 1 := by
  have h := rowsMatrix_eq_of_eqRows rows_B_cube
  rwa [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_idRows, rowsMatrix_rowsOf_seedB] at h

theorem matA_form : matAᵀ * formF * matA = formF := by
  have h := rowsMatrix_eq_of_eqRows rows_A_form
  rwa [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_transposeRows,
    rowsMatrix_rowsOf_seedA] at h

theorem matB_form : matBᵀ * formF * matB = formF := by
  have h := rowsMatrix_eq_of_eqRows rows_B_form
  rwa [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_transposeRows,
    rowsMatrix_rowsOf_seedB] at h

theorem matA_det_ne_zero : matA.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det matA_mul_self
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem matB_det_ne_zero : matB.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det matB_cube
  rw [Matrix.det_mul, Matrix.det_mul, h, zero_mul, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

noncomputable abbrev gA : GL (Fin 248) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero matA matA_det_ne_zero

noncomputable abbrev gB : GL (Fin 248) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero matB matB_det_ne_zero

noncomputable abbrev J : Subgroup (GL (Fin 248) (ZMod 2)) := Subgroup.closure {gA, gB}

@[expose] noncomputable def a : J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b : J := ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem a_val : ((a : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) = matA := rfl

theorem b_val : ((b : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) = matB := rfl

theorem closure_ab : Subgroup.closure ({a, b} : Set J) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA, gB} : Set (GL (Fin 248) (ZMod 2)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [a, b]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

noncomputable def thEquivJ : Blueprint.NativeSporadic.Th ≃* J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 2 248 (by norm_num) matA matB matA_det_ne_zero
    matB_det_ne_zero

end CFSG.Sporadic.Th
