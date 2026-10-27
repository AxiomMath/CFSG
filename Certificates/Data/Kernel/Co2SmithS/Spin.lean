module

public import Certificates.Data.CFSGNative.Co2Smith.Spin8
public import Certificates.Data.CFSGNative.Co2Smith.Sp6Pres

public section

namespace CFSG.KC.Co2SmithS

open CFSG.Sporadic.Co2Smith.Native

@[expose] def dot8 (r c : List Int) : Int :=
  r.getD 0 0 * c.getD 0 0 + r.getD 1 0 * c.getD 1 0 + r.getD 2 0 * c.getD 2 0 +
    r.getD 3 0 * c.getD 3 0 + r.getD 4 0 * c.getD 4 0 + r.getD 5 0 * c.getD 5 0 +
    r.getD 6 0 * c.getD 6 0 + r.getD 7 0 * c.getD 7 0

@[expose] def mulLC (R C : List (List Int)) : List (List Int) := C.map fun c => R.map fun r => dot8 r c

@[expose] def rowsL (A : Array Int) : List (List Int) :=
  (List.range 8).map fun i => (List.range 8).map fun j => A[8 * i + j]!

@[expose] def idC : List (List Int) :=
  (List.range 8).map fun j => (List.range 8).map fun i => if i = j then 1 else 0

@[expose] def negC : List (List Int) :=
  (List.range 8).map fun j => (List.range 8).map fun i => if i = j then -1 else 0

@[expose] def spinRows (k : Nat) : List (List Int) := rowsL (spinMats ())[k]!

@[expose] def wordC (w : List Nat) : List (List Int) :=
  w.foldr (fun k acc => mulLC (spinRows k) acc) idC

@[expose] def spinCheckK : Bool :=
  (List.range 8).all (fun i => wordC [2 * i, 2 * i + 1] == idC) &&
    (sp6CoverR ()).all (fun r => wordC (r.map sCode) == idC) && wordC [0, 0] == negC

end CFSG.KC.Co2SmithS

end
