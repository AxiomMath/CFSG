module

public import Certificates.Data.F4TwoSeitz

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434F42

open CFSG.LieType.Simplicity.TitsBits
open CFSG.RankThree.PartOne.SEITZX (codeBits)

@[expose] def eqB (A B : ℕ) : Bool := A % 2 ^ 2704 == B % 2 ^ 2704

@[expose] def wordB (gb : Array ℕ) (w : List ℕ) : ℕ :=
  w.foldl (fun acc l => mul acc gb[l]!) oneBits

@[expose] def distinctB : List ℕ → Bool
  | [] => true
  | a :: l => l.all (fun b => !eqB a b) && distinctB l

@[expose] def bfsAux (gb : Array ℕ) :
    ℕ → List (List ℕ × ℕ) → List (List ℕ × ℕ) → List (List ℕ × ℕ)
  | 0, known, _ => known
  | fuel + 1, known, frontier =>
    if frontier.isEmpty then known else
    let st := frontier.foldl (fun (acc : List (List ℕ × ℕ) × List (List ℕ × ℕ)) p =>
      (List.range gb.size).foldl (fun (acc : List (List ℕ × ℕ) × List (List ℕ × ℕ)) k =>
        let v := mul p.2 gb[k]!
        if acc.1.any (fun q => eqB q.2 v) then acc
        else ((p.1 ++ [k], v) :: acc.1, (p.1 ++ [k], v) :: acc.2)) acc) (known, [])
    bfsAux gb fuel st.1 st.2.reverse

@[expose] def bfs (gb : Array ℕ) (fuel : ℕ) : List (List ℕ) :=
  ((bfsAux gb fuel [([], oneBits)] [([], oneBits)]).map Prod.fst).reverse

@[expose] def enumOK (gb : Array ℕ) (L : List (List ℕ)) (vals : List ℕ) : Bool :=
  L.all (fun w => w.all fun l => decide (l < gb.size)) && decide (([] : List ℕ) ∈ L) &&
  vals.all (fun v => (List.range gb.size).all fun k => vals.any (eqB (mul v gb[k]!))) &&
  distinctB vals

@[expose] def elemAbOK (dgb : Array ℕ) : Bool :=
  (List.range dgb.size).all fun a =>
    eqB (mul dgb[a]! (mul dgb[a]! dgb[a]!)) oneBits &&
      (List.range dgb.size).all fun b => eqB (mul dgb[a]! dgb[b]!) (mul dgb[b]! dgb[a]!)

@[expose] def elemInfo (dV : List ℕ) (hps : List (ℕ × ℕ)) (v : ℕ) : ℕ × Bool × List Bool :=
  (v, eqB (mul v (mul v v)) oneBits,
    hps.map fun p => dV.any (eqB (mul (mul p.1 v) p.2)))

@[expose] def bothAny (la lb : List Bool) : Bool := (la.zip lb).any fun p => p.1 && p.2

@[expose] def pairOK (a b : ℕ × Bool × List Bool) : Bool :=
  !a.2.1 || !b.2.1 || eqB a.1 oneBits || eqB b.1 oneBits || eqB b.1 a.1 ||
  !eqB (mul a.1 b.1) (mul b.1 a.1) || eqB b.1 (mul a.1 a.1) || bothAny a.2.2 b.2.2

structure F42Data where
  gW : Array (List ℕ)
  qW : Array (List ℕ)
  qFuel : ℕ
  qOrd : ℕ
  dW : Array (List ℕ)
  dFuel : ℕ
  hW : Array (List ℕ)

@[expose] def gB (X : F42Data) : Array ℕ := X.gW.map codeBits

@[expose] def qgB (X : F42Data) : Array ℕ := X.qW.map (wordB (gB X))

@[expose] def qL (X : F42Data) : List (List ℕ) := bfs (qgB X) X.qFuel

@[expose] def qV (X : F42Data) : List ℕ := (qL X).map (wordB (qgB X))

@[expose] def dgB (X : F42Data) : Array ℕ := X.dW.map (wordB (qgB X))

@[expose] def dL (X : F42Data) : List (List ℕ) := bfs (dgB X) X.dFuel

@[expose] def dV (X : F42Data) : List ℕ := (dL X).map (wordB (dgB X))

@[expose] def hps (X : F42Data) : List (ℕ × ℕ) :=
  X.hW.toList.map fun w => (wordB (gB X) w, wordB (gB X) w.reverse)

@[expose] def f42Check' (X : F42Data) (gb qgb : Array ℕ) (qL : List (List ℕ)) (qV : List ℕ)
    (dgb : Array ℕ) (dL : List (List ℕ)) (dV : List ℕ) (infos : List (ℕ × Bool × List Bool)) :
    Bool :=
  (List.range gb.size).all (fun l => eqB (mul gb[l]! gb[l]!) oneBits) &&
  X.qW.toList.all (fun w => w.all fun l => decide (l < gb.size)) &&
  X.hW.toList.all (fun w => w.all fun l => decide (l < gb.size)) &&
  X.dW.toList.all (fun w => w.all fun l => decide (l < qgb.size)) &&
  enumOK qgb qL qV && decide (qL.length = X.qOrd) &&
  enumOK dgb dL dV && decide (81 ≤ dL.length) && elemAbOK dgb &&
  infos.all fun a => infos.all fun b => pairOK a b

@[expose] def f42Check (X : F42Data) : Bool :=
  f42Check' X (gB X) (qgB X) (qL X) (qV X) (dgB X) (dL X) (dV X)
    ((qV X).map (elemInfo (dV X) (hps X)))

end CFSG.RankThree.PartTwo.Sec4.Item434F42
