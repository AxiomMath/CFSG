module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinNoQ16E4Check
public import Std.Data.HashMap

public section

namespace Certificates.TwinPerpSmSp1

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord)
open CFSG.CGT.PushingUpLit.SolKNA.R4.Check (Q16Data qGens qCert)

structure Q8WitData where
  syl : Q16Data
  xg : Array (Array ℕ)
  cW : Array (List ℕ)

@[expose] def cands (D : Q8WitData) : Array (Array ℕ) := D.cW.map (posWord D.syl.n D.xg)

@[expose] def q8Elt (n : ℕ) (x y : Array ℕ) : ℕ → Array ℕ
  | 0 => idA n
  | 1 => x
  | 2 => compA n x x
  | 3 => compA n (compA n x x) x
  | 4 => y
  | 5 => compA n y x
  | 6 => compA n y (compA n x x)
  | _ => compA n y (compA n (compA n x x) x)

@[expose] def commA (n : ℕ) (a b : Array ℕ) : Bool := eqA n (compA n a b) (compA n b a)

@[expose] def outsideA (n : ℕ) (x y c a : Array ℕ) : Bool :=
  allLt 8 fun j => !eqA n (compA n c a) (compA n (q8Elt n x y j) c)

@[expose] def wit4 (n : ℕ) (x y c : Array ℕ) : Bool :=
  commA n c (compA n x x) && (outsideA n x y c x || outsideA n x y c y) &&
    (!commA n x (compA n (compA n c x) (invCand n c)) ||
      !commA n x (compA n (compA n c y) (invCand n c)) ||
      !commA n y (compA n (compA n c x) (invCand n c)) ||
      !commA n y (compA n (compA n c y) (invCand n c)))

@[expose] def wit5 (n : ℕ) (x y g : Array ℕ) : Bool :=
  (List.range 8).any fun j =>
    (!commA n (q8Elt n x y j) x || !commA n (q8Elt n x y j) y) &&
      commA n (compA n (compA n g (q8Elt n x y j)) (invCand n g)) (compA n x x) &&
      (outsideA n x y (compA n (compA n g (q8Elt n x y j)) (invCand n g)) x ||
        outsideA n x y (compA n (compA n g (q8Elt n x y j)) (invCand n g)) y)

@[expose] def q8WitFree (n : ℕ) (pts sq cs : Array (Array ℕ)) : Bool :=
  allLt pts.size fun i =>
    eqA n sq[i]! (idA n) || !eqA n (compA n sq[i]! sq[i]!) (idA n) ||
      allLt pts.size fun j =>
        !eqA n sq[j]! sq[i]! ||
          !eqA n (compA n pts[j]! pts[i]!) (compA n (invCand n pts[i]!) pts[j]!) ||
          cs.any fun c => wit4 n pts[i]! pts[j]! c || wit5 n pts[i]! pts[j]! c

@[expose] def q8WitCheck' (D : Q8WitData) (qg : Array (Array ℕ)) (cQ : ArrCert)
    (cs : Array (Array ℕ)) : Bool :=
  allLt D.syl.pg.size (fun k => validA D.syl.n D.syl.pg[k]!) &&
  D.syl.qKeys.all (fun p => decide (p < D.syl.n)) &&
  D.syl.qW.all (fun w => w.all fun l => decide (l < D.syl.pg.size)) &&
  enumOK D.syl.n qg D.syl.qKeys cQ && cQ.pts.size == D.syl.qOrd &&
  allLt D.xg.size (fun k => validA D.syl.n D.xg[k]!) &&
  D.cW.all (fun w => w.all fun l => decide (l < D.xg.size)) &&
  allLt cs.size (fun k => validA D.syl.n cs[k]!) &&
  q8WitFree D.syl.n cQ.pts (cQ.pts.map fun y => compA D.syl.n y y) cs

@[expose] def q8WitCheck (D : Q8WitData) : Bool :=
  q8WitCheck' D (qGens D.syl) (qCert D.syl) (cands D)

end Certificates.TwinPerpSmSp1
