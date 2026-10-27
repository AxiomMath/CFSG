module

public import CFSG.Quasithin.Background.HMathieuBits
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ASVolI.AppH

open CFSG.Quasithin.H.Mathieu

@[expose] def parF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, x => (x % 2) ^^^ parF k (x / 2)

@[expose] def par (x : ℕ) : ℕ := parF 16 x

structure KData where
  n : ℕ
  cols : List (List ℕ)
  lu : ℕ
  dU : ℕ
  xm : ℕ
  xb : List (ℕ × ℕ)

namespace KData

@[expose] def fixes (D : KData) (t m : ℕ) : Bool := actM (D.cols.getD t []) m == m

@[expose] def inU (D : KData) (m : ℕ) : Bool := D.lu.testBit m

@[expose] def inX (D : KData) (m : ℕ) : Bool := par (D.xm &&& m) == 0

@[expose] def ct (D : KData) (t : ℕ) : ℕ := (D.cols.getD t []).headD 0 ^^^ 1

@[expose] def chkCols (D : KData) : Bool :=
  decide (D.cols.length = 16) && decide D.cols.Nodup &&
  decide (D.cols.getD 0 [] = (List.range D.n).map fun j => 2 ^ j) &&
  D.cols.all fun c => decide (c.length = D.n) && c.all fun x => decide (x < 2 ^ D.n)

@[expose] def chkAb (D : KData) : Bool :=
  (List.range 16).all fun s => (List.range 16).all fun t =>
    (D.cols.getD s []).map (actM (D.cols.getD t [])) == (D.cols.getD t []).map (actM (D.cols.getD s [])) &&
    (D.cols.getD t []).map (actM (D.cols.getD t [])) == (List.range D.n).map fun j => 2 ^ j

@[expose] def chkLU (D : KData) : Bool :=
  (List.range (2 ^ D.n)).all fun m => D.inU m == (List.range 16).all fun t => D.fixes t m

@[expose] def chkCard (D : KData) : Bool :=
  decide (((List.range (2 ^ D.n)).filter D.inU).length = 2 ^ D.dU) &&
  decide (((List.range (2 ^ D.n)).filter D.inX).length = 2 ^ (D.n - 1))

@[expose] def chkCnt (D : KData) : Bool :=
  (List.range (2 ^ D.n)).all fun m =>
    D.inU m || (List.range 15).countP (fun i => D.fixes (i + 1) m) ≤ 1

@[expose] def chkEx (D : KData) : Bool :=
  (List.range 15).all fun i => (List.range (2 ^ D.n)).any fun m => D.fixes (i + 1) m && !D.inU m

@[expose] def chkXi (D : KData) : Bool :=
  (List.range (2 ^ D.n)).all fun m =>
    !((List.range 15).any fun i => D.fixes (i + 1) m) || D.inX m

@[expose] def chkXb (D : KData) : Bool :=
  D.xb.all (fun p => decide (1 ≤ p.2 ∧ p.2 < 16 ∧ p.1 < 2 ^ D.n) && D.fixes p.2 p.1 && D.inX p.1) &&
  (let cs := (combos (D.xb.map Prod.fst)).foldl (fun acc m => acc ||| (1 <<< m)) 0
   (List.range (2 ^ D.n)).all fun m => !D.inX m || cs.testBit m)

@[expose] def chkTV (D : KData) : Bool :=
  (List.range 16).all fun t => (List.range (2 ^ D.n)).all fun m =>
    let a := actM (D.cols.getD t []) m ^^^ m
    D.inU (if D.inX m then a else a ^^^ D.ct t)

@[expose] def chkCt (D : KData) : Bool :=
  (List.range 16).all (fun t => D.inX (D.ct t)) &&
  (List.range (2 ^ D.n)).all (fun m => !D.inX m || (List.range 16).any fun t => D.inU (m ^^^ D.ct t)) &&
  (List.range 15).all (fun i => !D.inU (D.ct (i + 1))) && !D.inX 1

@[expose] def good (D : KData) : Bool :=
  D.chkCols && D.chkAb && D.chkLU && D.chkCard && D.chkCnt && D.chkEx && D.chkXi && D.chkXb &&
    D.chkTV && D.chkCt

end KData

end CFSG.ASVolI.AppH
