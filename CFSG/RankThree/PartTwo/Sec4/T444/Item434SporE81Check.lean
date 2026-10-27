module

public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporE81

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def posWord (n : ℕ) (gs : Array (Array ℕ)) (w : List ℕ) : Array ℕ :=
  w.foldl (fun acc l => compA n acc gs[l]!) (idA n)

@[expose] def digitsOf (s : String) : List ℕ := s.toList.map fun c => c.toNat - 48

structure E81Data where
  n : ℕ
  pg : Array (Array ℕ)
  qW : Array (List ℕ)
  qKeys : List ℕ
  qFuel : ℕ
  qOrd : ℕ
  zW : List ℕ
  rW : Array (List ℕ)
  rKeys : List ℕ
  rFuel : ℕ
  rOrd : ℕ
  dW : Array (Array (List ℕ))
  dKeys : List ℕ
  dFuel : ℕ
  hW : Array (List ℕ)

@[expose] def qGens (X : E81Data) : Array (Array ℕ) := X.qW.map (posWord X.n X.pg)

@[expose] def qCert (X : E81Data) : ArrCert := enumBfs X.n (qGens X) X.qKeys X.qFuel

@[expose] def zArr (X : E81Data) : Array ℕ := posWord X.n (qGens X) X.zW

@[expose] def rGens (X : E81Data) : Array (Array ℕ) := X.rW.map (posWord X.n (qGens X))

@[expose] def rCert (X : E81Data) : ArrCert := enumBfs X.n (rGens X) X.rKeys X.rFuel

@[expose] def dPairs (X : E81Data) : Array (Array (Array ℕ) × ArrCert) :=
  X.dW.map fun ws =>
    let dg := ws.map (posWord X.n (qGens X))
    (dg, enumBfs X.n dg X.dKeys X.dFuel)

@[expose] def hArrs (X : E81Data) : Array (Array ℕ) := X.hW.map (posWord X.n X.pg)

@[expose] def coverOK (n : ℕ) (z : Array ℕ) (hs : Array (Array ℕ))
    (dps : Array (Array (Array ℕ) × ArrCert)) (s : Array ℕ) : Bool :=
  !eqA n (compA n s (compA n s s)) (idA n) || eqA n s (idA n) || eqA n s z ||
    eqA n s (compA n z z) ||
    hs.toList.any fun h =>
      let cs := conjA n h s
      let cz := conjA n h z
      dps.toList.any fun p => p.2.pts.toList.any (eqA n cs) && p.2.pts.toList.any (eqA n cz)

@[expose] def elemAbOK (n : ℕ) (dg : Array (Array ℕ)) : Bool :=
  allLt dg.size fun a =>
    eqA n (compA n dg[a]! (compA n dg[a]! dg[a]!)) (idA n) &&
      allLt dg.size fun b => eqA n (compA n dg[a]! dg[b]!) (compA n dg[b]! dg[a]!)

@[expose] def e81Check' (X : E81Data) (qg : Array (Array ℕ)) (cQ : ArrCert) (z : Array ℕ)
    (rg : Array (Array ℕ)) (cR : ArrCert) (dps : Array (Array (Array ℕ) × ArrCert))
    (hs : Array (Array ℕ)) : Bool :=
  allLt X.pg.size (fun k => validA X.n X.pg[k]!) &&
  (X.qKeys ++ X.rKeys ++ X.dKeys).all (fun p => decide (p < X.n)) &&
  X.qW.all (fun w => w.all fun l => decide (l < X.pg.size)) &&
  X.hW.all (fun w => w.all fun l => decide (l < X.pg.size)) &&
  X.zW.all (fun l => decide (l < qg.size)) &&
  X.rW.all (fun w => w.all fun l => decide (l < qg.size)) &&
  X.dW.all (fun ws => ws.all fun w => w.all fun l => decide (l < qg.size)) &&
  enumOK X.n qg X.qKeys cQ && cQ.pts.size == X.qOrd &&
  validA X.n z && eqA X.n (compA X.n z (compA X.n z z)) (idA X.n) && !eqA X.n z (idA X.n) &&
  allLt qg.size (fun k => eqA X.n (compA X.n z qg[k]!) (compA X.n qg[k]! z)) &&
  enumOK X.n rg X.rKeys cR && cR.pts.size == X.rOrd && decide (X.qOrd ≤ 3 * X.rOrd) &&
  dps.toList.all (fun p =>
    enumOK X.n p.1 X.dKeys p.2 && decide (81 ≤ p.2.pts.size) && elemAbOK X.n p.1) &&
  allLt hs.size (fun i => validA X.n hs[i]!) &&
  allLt cR.pts.size (fun k => coverOK X.n z hs dps cR.pts[k]!)

@[expose] def e81Check (X : E81Data) : Bool :=
  e81Check' X (qGens X) (qCert X) (zArr X) (rGens X) (rCert X) (dPairs X) (hArrs X)

end CFSG.RankThree.PartTwo.Sec4.Item434SporE81
