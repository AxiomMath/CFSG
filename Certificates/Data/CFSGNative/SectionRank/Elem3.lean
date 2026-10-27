module

public section

namespace CFSG.SectionRank.Native

set_option compiler.extract_closed false

inductive Op where
  | mul (i j k : Nat)
  | pow (e i k : Nat)
deriving Inhabited

@[expose] def Op.lt (n : Nat) : Op → Bool
  | .mul i j k => decide (i < n) && decide (j < n) && decide (k < n)
  | .pow _ i k => decide (i < n) && decide (k < n)

structure Ops (M V : Type) where
  decode : String → M
  mul : M → M → M
  one : M
  eq : M → M → Bool
  vmul : V → M → V
  unit : Nat → V
  vne : V → V → Bool

structure Data where
  seedA : String
  seedB : String
  nregs : Nat
  prog : List Op
  outs : List Nat
  tests : List Nat

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def pow (X : M) (e : Nat) : M :=
  if e = 0 then O.one
  else if e = 1 then X
  else
    let Y := pow (O.mul X X) (e / 2)
    if e % 2 = 1 then O.mul X Y else Y
termination_by e
decreasing_by omega

@[expose] def step [Inhabited M] (R : Array M) : Op → Array M
  | .mul i j k => R.set! k (O.mul R[i]! R[j]!)
  | .pow e i k => R.set! k (O.pow R[i]! e)

@[expose] def run [Inhabited M] (prog : List Op) (R : Array M) : Array M := prog.foldl O.step R

@[expose] def initRegs (A B : M) (n : Nat) : Array M :=
  Array.ofFn (n := n) fun r => if r.val = 0 then A else if r.val = 1 then B else O.one

@[expose] def app (X : M) : Nat → V → V
  | 0, v => v
  | n + 1, v => app X n (O.vmul v X)

@[expose] def appDigits : List M → Nat → V → V
  | [], _, v => v
  | X :: xs, n, v => appDigits xs (n / 3) (O.app X (n % 3) v)

@[expose] def moved (xs : List M) (n k : Nat) : Bool :=
  O.vne (O.appDigits xs n (O.unit k)) (O.unit k)

@[expose] def kerOK (xs : List M) (tests : List Nat) : Bool :=
  (List.range (3 ^ xs.length - 1)).all fun n => tests.any (O.moved xs (n + 1))

@[expose] def cubeOK (X : M) : Bool := O.eq (O.mul (O.mul X X) X) O.one

@[expose] def commOK (X Y : M) : Bool := O.eq (O.mul X Y) (O.mul Y X)

@[expose] def commsOK : List M → Bool
  | [] => true
  | X :: xs => xs.all (O.commOK X) && commsOK xs

@[expose] def elemOK (xs : List M) (tests : List Nat) : Bool :=
  xs.all O.cubeOK && O.commsOK xs && O.kerOK xs tests

@[expose] def check [Inhabited M] (D : Data) : Bool :=
  let R := O.run D.prog (O.initRegs (O.decode D.seedA) (O.decode D.seedB) D.nregs)
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && D.outs.all (decide <| · < D.nregs) &&
    O.elemOK (D.outs.map fun r => R[r]!) D.tests

end Ops

end CFSG.SectionRank.Native
