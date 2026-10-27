module

public import Certificates.Data.TripleM22Sylow
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace Certificates

open CFSG.Sporadic.Mathieu.Native
open CFSG.Sporadic.SmallF2
open CFSG.Sporadic.SmallF2.Native
open scoped Matrix

@[expose] abbrev SR (i : Fin 128) : Array Nat := sylowRows.getD i.val #[]

@[expose] abbrev MR (i : Fin 128) : Matrix (Fin 12) (Fin 12) (ZMod 2) := rowsMatrix 12 (SR i)

end Certificates
