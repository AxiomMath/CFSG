module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Check

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434O8pE9

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord elemAbOK)

structure E9Data where
  n : ℕ
  pg : Array (Array ℕ)
  qW : Array (List ℕ)
  qKeys : List ℕ
  qFuel : ℕ
  qOrd : ℕ
  dW : Array (List ℕ)
  dKeys : List ℕ
  dFuel : ℕ
  hW : Array (List ℕ)

@[expose] def qGens (X : E9Data) : Array (Array ℕ) := X.qW.map (posWord X.n X.pg)

@[expose] def qCert (X : E9Data) : ArrCert := enumBfs X.n (qGens X) X.qKeys X.qFuel

@[expose] def dGens (X : E9Data) : Array (Array ℕ) := X.dW.map (posWord X.n (qGens X))

@[expose] def dCert (X : E9Data) : ArrCert := enumBfs X.n (dGens X) X.dKeys X.dFuel

@[expose] def hArrs (X : E9Data) : Array (Array ℕ) := X.hW.map (posWord X.n X.pg)

@[expose] def covRow (n : ℕ) (cD : ArrCert) (h : Array ℕ) (cQ : ArrCert) : Array Bool :=
  cQ.pts.map fun q => cD.pts.toList.any (eqA n (conjA n h q))

@[expose] def cubeOne (n : ℕ) (cQ : ArrCert) : Array Bool :=
  cQ.pts.map fun x => eqA n (compA n x (compA n x x)) (idA n)

@[expose] def pairOK (n : ℕ) (cQ : ArrCert) (cb : Array Bool) (cov : Array (Array Bool))
    (a b : ℕ) : Bool :=
  !(cb[a]!) || !(cb[b]!) || eqA n cQ.pts[a]! (idA n) || eqA n cQ.pts[b]! (idA n) ||
  eqA n cQ.pts[b]! cQ.pts[a]! ||
  !eqA n (compA n cQ.pts[a]! cQ.pts[b]!) (compA n cQ.pts[b]! cQ.pts[a]!) ||
  eqA n cQ.pts[b]! (compA n cQ.pts[a]! cQ.pts[a]!) ||
  (List.range cov.size).any fun i => (cov[i]!)[a]! && (cov[i]!)[b]!

@[expose] def e9Check' (X : E9Data) (qg : Array (Array ℕ)) (cQ : ArrCert)
    (dg : Array (Array ℕ)) (cD : ArrCert) (hs : Array (Array ℕ)) (cb : Array Bool)
    (cov : Array (Array Bool)) : Bool :=
  allLt X.pg.size (fun k => validA X.n X.pg[k]!) &&
  (X.qKeys ++ X.dKeys).all (fun p => decide (p < X.n)) &&
  X.qW.all (fun w => w.all fun l => decide (l < X.pg.size)) &&
  X.hW.all (fun w => w.all fun l => decide (l < X.pg.size)) &&
  X.dW.all (fun w => w.all fun l => decide (l < qg.size)) &&
  enumOK X.n qg X.qKeys cQ && cQ.pts.size == X.qOrd &&
  enumOK X.n dg X.dKeys cD && decide (81 ≤ cD.pts.size) && elemAbOK X.n dg &&
  allLt hs.size (fun i => validA X.n hs[i]!) &&
  allLt cQ.pts.size (fun a => allLt cQ.pts.size fun b => pairOK X.n cQ cb cov a b)

@[expose] def e9Check (X : E9Data) : Bool :=
  e9Check' X (qGens X) (qCert X) (dGens X) (dCert X) (hArrs X) (cubeOne X.n (qCert X))
    ((hArrs X).map fun h => covRow X.n (dCert X) h (qCert X))

end CFSG.RankThree.PartTwo.Sec4.Item434O8pE9
