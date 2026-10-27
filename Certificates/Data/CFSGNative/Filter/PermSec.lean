module

public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.SectionRank.Native

set_option compiler.extract_closed false

@[expose] def permMul (n : Nat) (P Q : Array Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => P[Q[i.val]!]!

@[expose] def permId (n : Nat) : Array Nat := Array.ofFn (n := n) fun i => i.val

@[expose] def permOps (n : Nat) : Ops (Array Nat) Unit where
  decode _ := permId n
  mul := permMul n
  one := permId n
  eq X Y := X == Y
  vmul v _ := v
  unit _ := ()
  vne _ _ := false

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def sqOK (X : M) : Bool := O.eq (O.mul X X) O.one

@[expose] def prodDigits (b : Nat) : List M → Nat → M
  | [], _ => O.one
  | X :: xs, n => O.mul (O.pow X (n % b)) (prodDigits b xs (n / b))

@[expose] def prodKerOK (xs : List M) : Bool :=
  (List.range (2 ^ xs.length - 1)).all fun n => !O.eq (O.prodDigits 2 xs (n + 1)) O.one

@[expose] def invsOK (xs : List M) : Bool :=
  xs.all O.sqOK && O.commsOK xs && O.prodKerOK xs

@[expose] def invsCheck [Inhabited M] (A B : M) (nregs : Nat) (prog : List Op) (outs : List Nat) :
    Bool :=
  let R := O.run prog (O.initRegs A B nregs)
  decide (2 ≤ nregs) && prog.all (Op.lt nregs) && outs.all (decide <| · < nregs) &&
    O.invsOK (outs.map fun r => R[r]!)

end Ops

structure PermData where
  seedA : Array Nat
  seedB : Array Nat
  nregs : Nat
  prog : List Op
  outs : List Nat

@[expose] def permCheck (n : Nat) (D : PermData) : Bool :=
  (permOps n).invsCheck D.seedA D.seedB D.nregs D.prog D.outs

end CFSG.SectionRank.Native
