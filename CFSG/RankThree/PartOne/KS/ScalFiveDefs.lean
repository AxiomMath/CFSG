module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.PartOne.KS.ScalFive

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Sporadic.GLQ

structure Data (n : ℕ) where
  prog : List Instr
  nreg : ℕ
  iQ : Fin n → ℕ
  iZ : ℕ
  iS : ℕ
  iT : ℕ
  zWit : ℕ
  exM : Fin n → Fin n → ℕ
  exS : Fin n → Fin n → ℕ
  cs : Fin n → ℕ
  rT : ℕ
  ct : Fin n → ℕ
  e5 : Fin n → ℕ
  c5 : ℕ
  eTS : Fin n → ℕ
  cTS : ℕ

section Native

variable {M V : Type} (O : Ops M V)

@[expose] def allFin (n : ℕ) (f : Fin n → Bool) : Bool := (List.finRange n).all f

@[expose] def powOK (X : M) (e : ℕ) : Bool := O.eq (O.pow X e) O.one

@[expose] def commOK (X Y : M) : Bool := O.eq (O.mul X Y) (O.mul Y X)

@[expose] def neOne (X : M) (t : ℕ) : Bool := O.vne (O.vmul (O.unit t) X) (O.unit t)

@[expose] def pBcomm (a b : M × M) : M := O.mul (O.mul a.2 b.2) (O.mul a.1 b.1)

@[expose] def pConj (g a : M × M) : M := O.mul (O.mul g.2 a.1) g.1

@[expose] def prodPow {n : ℕ} (qs : Fin n → M) (z : M) (a : Fin n → ℕ) (c : ℕ) : M :=
  O.mul ((List.finRange n).foldr (fun j acc => O.mul (O.pow (qs j) (a j)) acc) O.one) (O.pow z c)

variable [Inhabited M]

@[expose] def relsOK {n : ℕ} (D : Data n) (R : Array (M × M)) : Bool :=
  powOK O R[D.iZ]!.1 5 && neOne O R[D.iZ]!.1 D.zWit &&
  allFin n (fun j => powOK O R[D.iQ j]!.1 5 && commOK O R[D.iQ j]!.1 R[D.iZ]!.1) &&
  allFin n (fun i => allFin n (fun j =>
    O.eq (pBcomm O R[D.iQ i]! R[D.iQ j]!) (O.pow R[D.iZ]!.1 (D.exM i j)))) &&
  allFin n (fun i => O.eq (pConj O R[D.iS]! R[D.iQ i]!)
    (prodPow O (fun j => R[D.iQ j]!.1) R[D.iZ]!.1 (D.exS i) (D.cs i))) &&
  allFin n (fun i => O.eq (pConj O R[D.iT]! R[D.iQ i]!)
    (O.mul (O.pow R[D.iQ i]!.1 D.rT) (O.pow R[D.iZ]!.1 (D.ct i)))) &&
  O.eq (O.pow R[D.iS]!.1 5) (prodPow O (fun j => R[D.iQ j]!.1) R[D.iZ]!.1 D.e5 D.c5) &&
  powOK O R[D.iT]!.1 4 &&
  O.eq (pBcomm O R[D.iT]! R[D.iS]!) (prodPow O (fun j => R[D.iQ j]!.1) R[D.iZ]!.1 D.eTS D.cTS)

end Native

end CFSG.RankThree.PartOne.KS.ScalFive
