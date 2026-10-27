module

public import Certificates.Data.CFSGNative.SectionRank.Local

public section

namespace CFSG.SectionRank.Native

set_option compiler.extract_closed false

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def enumBFS [Inhabited M] (gens : Array M) (cap : Nat) :
    Array M × Array Nat × Array Nat × Array (Array Nat) := Id.run do
  let mut E : Array M := #[O.one]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut cl : Array (Array Nat) := #[]
  for h in [0:cap] do
    if h < E.size then
      let X := E[h]!
      let mut row : Array Nat := #[]
      for g in [0:gens.size] do
        let Y := O.mul X gens[g]!
        match E.findIdx? (fun Z => O.eq Y Z) with
        | some j => row := row.push j
        | none =>
          row := row.push E.size
          E := E.push Y
          par := par.push h
          lab := lab.push g
      cl := cl.push row
  return (E, par, lab, cl)

@[expose] def enumOK [Inhabited M] [Inhabited V] (gens : Array M) (n t : Nat) (E : Array M)
    (par lab : Array Nat) (cl : Array (Array Nat)) : Bool :=
  E.size == n && par.size == n && lab.size == n && cl.size == n && decide (0 < n) &&
    O.eq E[0]! O.one &&
    (List.range n).all (fun i => i == 0 || (decide (par[i]! < i) &&
      decide (lab[i]! < gens.size) && O.eq E[i]! (O.mul E[par[i]!]! gens[lab[i]!]!))) &&
    (List.range n).all (fun i => (List.range gens.size).all fun g =>
      decide (cl[i]![g]! < n) && O.eq (O.mul E[i]! gens[g]!) E[cl[i]![g]!]!) &&
    O.distinctOK (E.map fun X => O.vmul (O.unit t) X)

@[expose] def memOK [Inhabited M] (E : Array M) (X : M) : Bool :=
  (List.range E.size).any fun j => O.eq X E[j]!

@[expose] def conjMemOK [Inhabited M] (E : Array M) (H X : M) : Bool :=
  (List.range E.size).any fun j => O.conjOK H X E[j]!

@[expose] def notMemOK [Inhabited M] (E : Array M) (X : M) (t : Nat) : Bool :=
  (List.range E.size).all fun j => O.vne (O.vmul (O.unit t) X) (O.vmul (O.unit t) E[j]!)

end Ops

structure LocDetData where
  seedA : String
  seedB : String
  nregs : Nat
  prog : List Op
  rk1 : Nat
  rk2 : Nat
  ok1 : Nat
  ok2 : Nat
  nK : Nat
  rx : Nat
  ry : Nat
  rh : Nat
  oh : Nat
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  rc : Nat
  ru1 : Nat
  rv1 : Nat
  ru2 : Nat
  rv2 : Nat
  t : Nat

@[expose] def LocDetData.regsLt (D : LocDetData) : Bool :=
  [D.rk1, D.rk2, D.rx, D.ry, D.rh, D.rc, D.ru1, D.rv1, D.ru2, D.rv2].all (decide <| · < D.nregs)

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def genFacts (D : LocDetData) (K1 K2 : M) : Bool :=
  decide (0 < D.ok1) && decide (0 < D.ok2) && O.eq (O.pow K1 D.ok1) O.one &&
    O.eq (O.pow K2 D.ok2) O.one

@[expose] def qFacts [Inhabited M] [Inhabited V] (E : Array M) (X Y : M) (t : Nat) : Bool :=
  O.memOK E X && O.memOK E Y && O.eq (O.pow X 3) O.one && O.eq (O.pow Y 3) O.one &&
    O.eq (O.mul X Y) (O.mul Y X) && O.normalFormOK 3 [X, Y] t

@[expose] def hFacts [Inhabited M] (D : LocDetData) (E : Array M) (K1 K2 X Y H : M) : Bool :=
  decide (0 < D.oh) && O.eq (O.pow H D.oh) O.one && O.conjMemOK E H K1 && O.conjMemOK E H K2 &&
    O.conjOK H X (O.mul (O.pow X D.a) (O.pow Y D.c)) &&
    O.conjOK H Y (O.mul (O.pow X D.b) (O.pow Y D.d))

@[expose] def cFacts [Inhabited M] (E : Array M) (K1 K2 C : M) (t : Nat) : Bool :=
  O.eq (O.pow C 3) O.one && O.vne (O.vmul (O.unit t) C) (O.unit t) &&
    O.eq (O.mul C K1) (O.mul K1 C) && O.eq (O.mul C K2) (O.mul K2 C) && O.notMemOK E C t &&
    O.notMemOK E (O.mul C C) t

@[expose] def perfFacts [Inhabited M] (E : Array M) (K U W : M) : Bool :=
  O.memOK E U && O.memOK E W && O.eq (O.mul U W) (O.mul (O.mul K W) U)

@[expose] def localDetFacts [Inhabited M] [Inhabited V] (D : LocDetData) (R E : Array M)
    (par lab : Array Nat) (cl : Array (Array Nat)) : Bool :=
  O.genFacts D R[D.rk1]! R[D.rk2]! &&
    O.enumOK #[R[D.rk1]!, R[D.rk2]!] D.nK D.t E par lab cl &&
    O.qFacts E R[D.rx]! R[D.ry]! D.t &&
    O.hFacts D E R[D.rk1]! R[D.rk2]! R[D.rx]! R[D.ry]! R[D.rh]! &&
    O.cFacts E R[D.rk1]! R[D.rk2]! R[D.rc]! D.t &&
    O.perfFacts E R[D.rk1]! R[D.ru1]! R[D.rv1]! && O.perfFacts E R[D.rk2]! R[D.ru2]! R[D.rv2]!

@[expose] def localDetCheck [Inhabited M] [Inhabited V] (D : LocDetData) : Bool :=
  let R := O.regsOf D.seedA D.seedB D.nregs D.prog
  let En := O.enumBFS #[R[D.rk1]!, R[D.rk2]!] D.nK
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && D.regsLt &&
    O.localDetFacts D R En.1 En.2.1 En.2.2.1 En.2.2.2

end Ops

end CFSG.SectionRank.Native
