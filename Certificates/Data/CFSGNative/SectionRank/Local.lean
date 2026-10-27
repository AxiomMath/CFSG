module

public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.SectionRank.Native

set_option compiler.extract_closed false

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def appBase (b : Nat) : List M → Nat → V → V
  | [], _, v => v
  | X :: xs, n, v => appBase b xs (n / b) (O.app X (n % b) v)

@[expose] def distinctOK [Inhabited V] (vs : Array V) : Bool :=
  (List.range vs.size).all fun i => (List.range i).all fun j => O.vne vs[i]! vs[j]!

@[expose] def normalFormOK [Inhabited V] (b : Nat) (xs : List M) (t : Nat) : Bool :=
  O.distinctOK (Array.ofFn (n := b ^ xs.length) fun n => O.appBase b xs n.val (O.unit t))

@[expose] def conjOK (X Y W : M) : Bool := O.eq (O.mul X Y) (O.mul W X)

end Ops

structure SqData where
  seedA : String
  seedB : String
  nregs : Nat
  prog : List Op
  rx : Nat
  ry : Nat
  rh : Nat
  r : Nat
  oh : Nat
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  t : Nat

structure CubData where
  seedA : String
  seedB : String
  nregs : Nat
  prog : List Op
  rx : Nat
  ry : Nat
  rh : Nat
  r : Nat
  oh : Nat
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  k : Nat
  l : Nat
  μ : Nat
  t : Nat

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def regsOf [Inhabited M] (seedA seedB : String) (nregs : Nat) (prog : List Op) :
    Array M :=
  O.run prog (O.initRegs (O.decode seedA) (O.decode seedB) nregs)

@[expose] def squareCheck [Inhabited M] [Inhabited V] (D : SqData) : Bool :=
  let R := O.regsOf D.seedA D.seedB D.nregs D.prog
  let X := R[D.rx]!
  let Y := R[D.ry]!
  let H := R[D.rh]!
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && decide (D.rx < D.nregs) &&
    decide (D.ry < D.nregs) && decide (D.rh < D.nregs) && decide (0 < D.r) &&
    decide (0 < D.oh) && O.eq (O.pow X D.r) O.one && O.eq (O.pow Y D.r) O.one &&
    O.eq (O.pow H D.oh) O.one && O.eq (O.mul X Y) (O.mul Y X) &&
    O.conjOK H X (O.mul (O.pow X D.a) (O.pow Y D.c)) &&
    O.conjOK H Y (O.mul (O.pow X D.b) (O.pow Y D.d)) && O.normalFormOK D.r [X, Y] D.t

@[expose] def commM (r : Nat) (X Y : M) : M :=
  O.mul (O.mul (O.mul X Y) (O.pow X (r - 1))) (O.pow Y (r - 1))

@[expose] def cubicCheck [Inhabited M] [Inhabited V] (D : CubData) : Bool :=
  let R := O.regsOf D.seedA D.seedB D.nregs D.prog
  let X := R[D.rx]!
  let Y := R[D.ry]!
  let H := R[D.rh]!
  let Z := O.commM D.r X Y
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && decide (D.rx < D.nregs) &&
    decide (D.ry < D.nregs) && decide (D.rh < D.nregs) && decide (0 < D.r) &&
    decide (0 < D.oh) && O.eq (O.pow X D.r) O.one && O.eq (O.pow Y D.r) O.one &&
    O.eq (O.pow H D.oh) O.one && O.vne (O.vmul (O.unit D.t) Z) (O.unit D.t) &&
    O.eq (O.mul Z X) (O.mul X Z) && O.eq (O.mul Z Y) (O.mul Y Z) &&
    O.conjOK H X (O.mul (O.mul (O.pow X D.a) (O.pow Y D.b)) (O.pow Z D.k)) &&
    O.conjOK H Y (O.mul (O.mul (O.pow X D.c) (O.pow Y D.d)) (O.pow Z D.l)) &&
    O.conjOK H Z (O.pow Z D.μ) && O.normalFormOK D.r [X, Y, Z] D.t

end Ops

end CFSG.SectionRank.Native
