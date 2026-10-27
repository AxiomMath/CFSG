module

public import CFSG.Sporadic.Schreier.Co3Outer
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public meta import CFSG.Sporadic.Schreier.Co3Outer
public meta import Mathlib.Data.Matrix.Block
public meta import CFSG.Sporadic.Schreier.Co3Cert
public import CFSG.Sporadic.Schreier.Co3Cert
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native Matrix

@[expose] def co3Vec6 (n : ℕ) : Co3V6 := fun c => if n.testBit (co3Idx6 c) then 1 else 0

@[expose] def co3Sp6J (n : ℕ) : ℕ := ((n &&& 7) <<< 3) ||| ((n >>> 3) &&& 7)

@[expose] def co3Sp36BaseArr : Array Nat :=
  ((co3FinList 36 (by decide) co3Sp36Base).map Fin.val).toArray

end CFSG.Sporadic.Schreier.Co3
