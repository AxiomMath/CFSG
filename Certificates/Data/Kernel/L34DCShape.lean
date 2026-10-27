module

public import Certificates.Data.L34DC

public section

namespace Certificates.L34DC

@[expose] def allN5167 (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec true (fun i acc => p i && acc) n

@[expose] def eltN (n : Nat) : Elt := elt ⟨n % 192, Nat.mod_lt _ (by decide)⟩

@[expose] def shapeOK5167 (y z : Nat) : Bool :=
  (y / 4 % 4 == 0) && (y / 16 != 0) && (z / 4 != 0)

@[expose] def pairOK5167 (y z : Nat) : Bool :=
  shapeOK5167 y z || !(mulE (eltN y) (eltN y) == one) ||
    (mulE (mulE (eltN y) (eltN z)) (mulE (eltN y) (eltN z)) == one)

@[expose] def pairsOK5167 : Bool :=
  allN5167 64 fun y => allN5167 16 fun z => pairOK5167 y z

@[expose] def idemOK5167 : Bool :=
  allN5167 192 fun i => (i == 0) || !(mulE (eltN i) (eltN i) == eltN i)

@[expose] def checkShape5167 : Bool := idemOK5167 && pairsOK5167

end Certificates.L34DC
