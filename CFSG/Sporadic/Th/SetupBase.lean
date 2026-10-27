
module

public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public meta import Certificates.Data.CFSGNative.Th.Certificate
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Th

open Native Matrix

noncomputable abbrev matA : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 248 1 Blueprint.NativeSporadic.ThSeed1

noncomputable abbrev matB : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 248 1 Blueprint.NativeSporadic.ThSeed2

private theorem seedA_eq' : seedA = Blueprint.NativeSporadic.ThSeed1 := rfl

private theorem seedB_eq' : seedB = Blueprint.NativeSporadic.ThSeed2 := rfl

theorem seedA_eq : seedA = Blueprint.NativeSporadic.ThSeed1 := seedA_eq'

theorem seedB_eq : seedB = Blueprint.NativeSporadic.ThSeed2 := seedB_eq'

theorem rowsMatrix_rowsOf_seedA : rowsMatrix (rowsOf seedA) = matA := by
  rw [rowsMatrix_rowsOf, seedA_eq]

theorem rowsMatrix_rowsOf_seedB : rowsMatrix (rowsOf seedB) = matB := by
  rw [rowsMatrix_rowsOf, seedB_eq]

noncomputable abbrev formF : Matrix (Fin 248) (Fin 248) (ZMod 2) := rowsMatrix fcRows

end CFSG.Sporadic.Th
