module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocLinCheck
public import Mathlib.GroupTheory.Perm.Basic
public import Std.Data.HashMap

public section

namespace Certificates.L43TwinQ8

open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc CFSG.Monster.B.Fischer

@[expose] def gens : Array (Array ℕ) :=
  #[#[2, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      1, 0],
    #[0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      1, 0],
    #[0, 0, 2, 0, 0, 0, 1, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0,
      0, 0],
    #[0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2,
      0, 1]]

@[expose] def t0 : Array ℕ :=
  #[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2,
    0]

@[expose] def q1a : Array ℕ :=
  #[0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1,
    0]

@[expose] def q1b : Array ℕ :=
  #[1, 1, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2, 2, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1,
    0]

@[expose] def q2a : Array ℕ :=
  #[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0,
    0]

@[expose] def q2b : Array ℕ :=
  #[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 2, 1,
    0]

@[expose] def wc : Array ℕ :=
  #[2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2,
    0]

@[expose] def bfs (_ : Unit := ()) : ArrCert :=
  arrBfs (locAct 4 gens) gens.size (eltKey 4) (eltOne 4) 600

@[expose] def q8Words (a b : Array ℕ) : List (Array ℕ) :=
  [eltOne 4, eltMul 4 a a, a, eltInv 4 a, b, eltInv 4 b, eltMul 4 a b, eltMul 4 b a]

@[expose] def memQ8 (x a b : Array ℕ) : Bool := (q8Words a b).any fun z => eltEq 4 x z

@[expose] def commutes (x y : Array ℕ) : Bool := eltEq 4 (eltMul 4 x y) (eltMul 4 y x)

@[expose] def sameQ8 (a b qa qb : Array ℕ) : Bool :=
  memQ8 a qa qb && memQ8 b qa qb && memQ8 qa a b && memQ8 qb a b

@[expose] def omega4Wit (a b : Array ℕ) : Bool :=
  let ca := eltConj 4 wc a
  let cb := eltConj 4 wc b
  (!memQ8 ca a b || !memQ8 cb a b) &&
    (!commutes a ca || !commutes a cb || !commutes b ca || !commutes b cb)

@[expose] def pairOK (a b : Array ℕ) : Bool :=
  !eltEq 4 (eltConj 4 b a) (eltInv 4 a) || sameQ8 a b q1a q1b || sameQ8 a b q2a q2b ||
    omega4Wit a b

@[expose] def pairsOK (pts : Array (Array ℕ)) : Bool :=
  let idx := (List.range pts.size).filter fun i => eltEq 4 (eltMul 4 pts[i]! pts[i]!) t0
  idx.all fun i => idx.all fun j => pairOK pts[i]! pts[j]!

@[expose] def check (_ : Unit := ()) : Bool :=
  let c := bfs ()
  (List.range gens.size).all (fun k => eltValid 4 gens[k]!) &&
    arrCertOK (locAct 4 gens) gens.size (eltValid 4) (eltKey 4) (eltOne 4) c &&
    c.pts.size == 2 ^ 9 &&
    eltValid 4 t0 && eltValid 4 q1a && eltValid 4 q1b && eltValid 4 q2a && eltValid 4 q2b &&
    eltValid 4 wc && eE 4 wc == 0 && inF4 wc &&
    (List.range gens.size).all (fun k => commutes gens[k]! t0) && commutes wc t0 &&
    pairsOK c.pts

end Certificates.L43TwinQ8
