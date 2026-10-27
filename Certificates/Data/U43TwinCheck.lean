module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Data
public import Certificates.Data.U43TwinData
public import Mathlib.GroupTheory.Perm.Basic
public import Std.Data.HashMap

public section

namespace Certificates.U43Twin

open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check CFSG.Monster.B.Fischer

@[expose] def innerShape (x : Array ℕ) : Bool := x[16]! == 0 && detC x == 3

@[expose] def commC (x y : Array ℕ) : Bool := eqZ (mulRaw x y) (mulRaw y x)

@[expose] def conjBy (c x : Array ℕ) : Array ℕ := mulRaw (mulRaw c x) (conjT c)

@[expose] def invertC (c : Array ℕ) : Bool :=
  rawValid c && rawValid (conjT c) && isZ (mulRaw c (conjT c))

@[expose] def memL (x : Array ℕ) (L : List (Array ℕ)) : Bool := L.any fun y => eqZ x y

@[expose] def q8Elts (p q : Array ℕ) : List (Array ℕ) :=
  [idCode, p, powRaw p 2, powRaw p 3, q, mulRaw q p, mulRaw q (powRaw p 2), mulRaw q (powRaw p 3)]

@[expose] def q8PairC (p q : Array ℕ) : Bool :=
  eqZ (mulRaw p p) T0 && eqZ (mulRaw q q) T0 && eqZ (mulRaw q p) (mulRaw (mulRaw T0 p) q)

@[expose] def evenC (w : Array ℕ) : Bool :=
  (isZ (powRaw w 2) && !isZ w) || (isZ (powRaw w 4) && !isZ (powRaw w 2))

@[expose] def violC (E : List (Array ℕ)) (c : Array ℕ) : Bool :=
  let F := E.map (conjBy c)
  (F.any fun y => !memL y E) &&
    ((E.any fun x => F.any fun y => !commC x y) || (F.any fun y => memL y E && !isZ (mulRaw y y)))

@[expose] def actConj (k : ℕ) (a : Array ℕ) : Array ℕ :=
  normalize (mulRaw (mulRaw gI[k]! a) gIinv[k]!)

@[expose] def orbCert (_ : Unit := ()) : ArrCert := arrBfs actConj gI.size keyOf T0 3000

@[expose] def orbOK (_ : Unit := ()) : Bool :=
  (List.range gI.size).all (fun k => rawValid gI[k]! && rawValid gIinv[k]! &&
      innerShape gI[k]! && isZ (mulRaw gI[k]! gIinv[k]!)) &&
    (let c := orbCert ()
     arrCertOK actConj gI.size valid keyOf T0 c && c.pts.size == 2835)

@[expose] def cCert (_ : Unit := ()) : ArrCert := arrBfs (act gC) gC.size keyOf idCode 1300

@[expose] def cOK (_ : Unit := ()) : Bool :=
  (List.range gC.size).all (fun k => rawValid gC[k]! && innerShape gC[k]! && commC gC[k]! T0) &&
    (let c := cCert ()
     arrCertOK (act gC) gC.size valid keyOf idCode c && c.pts.size == 1152)

@[expose] def t0OK (_ : Unit := ()) : Bool :=
  rawValid T0 && innerShape T0 && isZ (mulRaw T0 T0) && !isZ T0 &&
    (List.range u43Data.gens.size).all fun k => commC u43Data.gens[k]! T0

@[expose] def qOK (_ : Unit := ()) : Bool :=
  [P1, Q1, P2, Q2].all (fun x => rawValid x && innerShape x) && q8PairC P1 Q1 && q8PairC P2 Q2 &&
    invertC G0 && innerShape G0 && commC G0 T0 &&
    memL (conjBy G0 P2) (q8Elts P1 Q1) && memL (conjBy G0 Q2) (q8Elts P1 Q1)

@[expose] def candsOK (_ : Unit := ()) : Bool :=
  q8Cands.toList.all fun c => invertC c && innerShape c && commC c T0

@[expose] def tCert (_ : Unit := ()) : ArrCert := arrBfs (act gT) gT.size keyOf idCode 200

@[expose] def tOK (_ : Unit := ()) : Bool :=
  (List.range gT.size).all (fun k => rawValid gT[k]! && innerShape gT[k]!) &&
    (let c := tCert ()
     arrCertOK (act gT) gT.size valid keyOf idCode c && c.pts.size == 128)

@[expose] def invOK (_ : Unit := ()) : Bool :=
  let pts := (tCert ()).pts
  (List.range pts.size).all fun i =>
    !(isZ (mulRaw pts[i]! pts[i]!) && !isZ pts[i]!) ||
      invCands.toList.any fun e => rawValid e && eqZ (mulRaw e pts[i]!) (mulRaw T0 e)

@[expose] def q8OK (_ : Unit := ()) : Bool :=
  let pts := (bfs u43Data).pts
  let sq := (List.range pts.size).filter fun i => eqZ (mulRaw pts[i]! pts[i]!) T0
  let E1 := q8Elts P1 Q1
  let E2 := q8Elts P2 Q2
  sq.all fun i => sq.all fun j =>
    !eqZ (mulRaw pts[j]! pts[i]!) (mulRaw (mulRaw T0 pts[i]!) pts[j]!) ||
      (memL pts[i]! E1 && memL pts[j]! E1) || (memL pts[i]! E2 && memL pts[j]! E2) ||
      q8Cands.toList.any fun c => violC (q8Elts pts[i]! pts[j]!) c

@[expose] def permOK (_ : Unit := ()) : Bool :=
  let pts := (cCert ()).pts
  let E1 := q8Elts P1 Q1
  let E2 := q8Elts P2 Q2
  (List.range pts.size).all fun i =>
    invertC pts[i]! &&
      ((memL (conjBy pts[i]! P1) E1 && memL (conjBy pts[i]! Q1) E1) ||
        (memL (conjBy pts[i]! P1) E2 && memL (conjBy pts[i]! Q1) E2))

@[expose] def oddOK (_ : Unit := ()) : Bool :=
  let pts := (cCert ()).pts
  let G := q8Elts P1 Q1 ++ q8Elts P2 Q2
  (List.range pts.size).all fun i =>
    isZ pts[i]! || !isZ (powRaw pts[i]! 9) ||
      G.any fun g => evenC (mulRaw (mulRaw (mulRaw pts[i]! g) (powRaw pts[i]! 8)) (powRaw g 3))

@[expose] def slQuads : List (ℕ × ℕ × ℕ × ℕ) :=
  ((List.range 81).map fun k => (k / 27, k / 9 % 3, k / 3 % 3, k % 3)).filter fun m =>
    (m.1 * m.2.2.2 + 2 * (m.2.1 * m.2.2.1)) % 3 == 1

@[expose] def qidx (m : ℕ × ℕ × ℕ × ℕ) : ℕ := 27 * m.1 + 9 * m.2.1 + 3 * m.2.2.1 + m.2.2.2

@[expose] def qmul (m n : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  ((m.1 * n.1 + m.2.1 * n.2.2.1) % 3, (m.1 * n.2.1 + m.2.1 * n.2.2.2) % 3,
    (m.2.2.1 * n.1 + m.2.2.2 * n.2.2.1) % 3, (m.2.2.1 * n.2.1 + m.2.2.2 * n.2.2.2) % 3)

@[expose] def psiOK (_ : Unit := ()) : Bool :=
  (slQuads.all fun m => rawValid psiTab[qidx m]! && innerShape psiTab[qidx m]! &&
      commC psiTab[qidx m]! P2 && commC psiTab[qidx m]! Q2 &&
      (m == (1, 0, 0, 1) || !isZ psiTab[qidx m]!)) &&
    slQuads.all fun m => slQuads.all fun n =>
      eqZ psiTab[qidx (qmul m n)]! (mulRaw psiTab[qidx m]! psiTab[qidx n]!)

@[expose] def centOK (_ : Unit := ()) : Bool :=
  let pts := (cCert ()).pts
  let psiL := slQuads.map fun m => psiTab[qidx m]!
  (List.range pts.size).all fun i =>
    (!(commC pts[i]! P2 && commC pts[i]! Q2) || memL pts[i]! psiL) &&
      (!(commC pts[i]! P1 && commC pts[i]! Q1) || memL pts[i]! H2tab.toList)

@[expose] def commOK (_ : Unit := ()) : Bool :=
  H2tab.toList.all fun h => rawValid h && slQuads.all fun m => commC psiTab[qidx m]! h

@[expose] def allOK (_ : Unit := ()) : Bool :=
  t0OK () && qOK () && orbOK () && cOK () && tOK () && candsOK () && invOK () && q8OK () &&
    permOK () && oddOK () && psiOK () && centOK () && commOK ()

end Certificates.U43Twin
