module

public import Certificates.Data.CFSGNative.SectionRank.Local

public section

namespace CFSG.SectionRank.Native

set_option compiler.extract_closed false

structure SecData where
  seedA : String
  seedB : String
  nregs : Nat
  prog : List Op
  outs : List Nat
  tReg : Nat
  tests : List Nat

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def inN (T X : M) : Bool := O.eq X O.one || O.eq X T

@[expose] def commModOK (T X Y : M) : Bool :=
  O.eq (O.mul X Y) (O.mul Y X) || O.eq (O.mul X Y) (O.mul T (O.mul Y X))

@[expose] def commsModOK (T : M) : List M → Bool
  | [] => true
  | X :: xs => xs.all (O.commModOK T X) && commsModOK T xs

@[expose] def outsideN (T : M) (xs : List M) (tests : List Nat) (n : Nat) : Bool :=
  tests.any (fun k => O.vne (O.appBase 2 xs n (O.unit k)) (O.unit k)) &&
    tests.any (fun k => O.vne (O.appBase 2 xs n (O.unit k)) (O.vmul (O.unit k) T))

@[expose] def kerModOK (T : M) (xs : List M) (tests : List Nat) : Bool :=
  (List.range (2 ^ xs.length - 1)).all fun n => O.outsideN T xs tests (n + 1)

@[expose] def secOK (T : M) (xs : List M) (tests : List Nat) : Bool :=
  O.eq (O.mul T T) O.one &&
    xs.all (fun X => O.eq (O.mul X T) (O.mul T X) && O.inN T (O.mul X X)) &&
    O.commsModOK T xs && O.kerModOK T xs tests

@[expose] def secCheck [Inhabited M] (D : SecData) : Bool :=
  let R := O.run D.prog (O.initRegs (O.decode D.seedA) (O.decode D.seedB) D.nregs)
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && D.outs.all (decide <| · < D.nregs) &&
    decide (D.tReg < D.nregs) && O.secOK R[D.tReg]! (D.outs.map fun r => R[r]!) D.tests

end Ops

end CFSG.SectionRank.Native
