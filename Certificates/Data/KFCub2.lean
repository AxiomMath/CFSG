module

public import Certificates.Data.CFSGNative.SectionRank.Local

public section

namespace CFSG.SectionRank.Native

set_option compiler.extract_closed false

structure Cub2NormData where
  rh : Nat
  oh : Nat
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  k : Nat
  l : Nat

structure Cub2Data where
  seedA : String
  seedB : String
  nregs : Nat
  prog : List Op
  rx : Nat
  ry : Nat
  r : Nat
  t : Nat
  h1 : Cub2NormData
  h2 : Cub2NormData

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def normOK [Inhabited M] (N : Cub2NormData) (nregs : Nat) (R : Array M) (X Y Z : M) : Bool :=
  decide (N.rh < nregs) && decide (0 < N.oh) && O.eq (O.pow R[N.rh]! N.oh) O.one &&
    O.conjOK R[N.rh]! X (O.mul (O.mul (O.pow X N.a) (O.pow Y N.b)) (O.pow Z N.k)) &&
    O.conjOK R[N.rh]! Y (O.mul (O.mul (O.pow X N.c) (O.pow Y N.d)) (O.pow Z N.l))

@[expose] def cub2Check [Inhabited M] [Inhabited V] (D : Cub2Data) : Bool :=
  let R := O.regsOf D.seedA D.seedB D.nregs D.prog
  let X := R[D.rx]!
  let Y := R[D.ry]!
  let Z := O.commM D.r X Y
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && decide (D.rx < D.nregs) &&
    decide (D.ry < D.nregs) && decide (0 < D.r) && O.eq (O.pow X D.r) O.one &&
    O.eq (O.pow Y D.r) O.one && O.vne (O.vmul (O.unit D.t) Z) (O.unit D.t) &&
    O.eq (O.mul Z X) (O.mul X Z) && O.eq (O.mul Z Y) (O.mul Y Z) &&
    O.normOK D.h1 D.nregs R X Y Z && O.normOK D.h2 D.nregs R X Y Z

end Ops

end CFSG.SectionRank.Native
