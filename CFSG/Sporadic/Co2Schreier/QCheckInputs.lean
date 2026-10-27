module

public import CFSG.Sporadic.Co2Schreier.WitCheck
public import CFSG.Sporadic.Co2Schreier.SylowCheck
public import Certificates.Data.CFSGNative.HS.SmallF2
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheck
public meta import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.SmallF2.Native

@[expose] def qActRows (W : WitCert) (i : ℕ) : Array ℕ :=
  (W.wLocal.qQuotientActionRows.getD i []).toArray

@[expose] def qActCols (W : WitCert) (i : ℕ) : Array ℕ := transposeRows 8 (qActRows W i)

@[expose] def qCol (W : WitCert) (i l : ℕ) : ℕ := (qActCols W i)[l]?.getD 0

@[expose] def bits8 (w : ℕ) : List ℕ := (List.range 8).filter fun k => w.testBit k

@[expose] def qProdArr (w : ℕ) : Array ℕ := prodArr qArrs (bits8 w)

@[expose] def isOneOrZ (t : Array ℕ) : Bool := eqA 2300 t (idA 2300) || eqA 2300 t zArr

@[expose] def isProdOrZ (t : Array ℕ) (w : ℕ) : Bool :=
  eqA 2300 t (qProdArr w) || eqA 2300 t (compA 2300 (qProdArr w) zArr)

@[expose] def spanIns (S x : ℕ) : ℕ :=
  if S.testBit x then S else
    (List.range 256).foldl (fun acc a => if S.testBit a then acc ||| (1 <<< (a ^^^ x)) else acc)
      S

@[expose] def spanStep (T0 T1 : Array ℕ) (S : ℕ) : ℕ :=
  (List.range 256).foldl (fun acc a =>
    if S.testBit a then spanIns (spanIns acc (vecMulN 8 T0 a)) (vecMulN 8 T1 a) else acc) S

@[expose] def spanIter (T0 T1 : Array ℕ) : ℕ → ℕ → ℕ
  | 0, S => S
  | n + 1, S => spanIter T0 T1 n (spanStep T0 T1 S)

@[expose] def thetaN (W : WitCert) (a : ℕ) : ℕ :=
  a ^^^ vecMulN 8 (qActCols W 0) a ^^^ vecMulN 8 (qActCols W 1) a

@[noinline, expose] def qmodCheck (W : WitCert) : Bool :=
  W.wLocal.qQuotientBasisIndices == [1, 2, 3, 4, 5, 6, 7, 8] &&
    allLt 8 (fun k => isOneOrZ (compA 2300 qArrs[k]! qArrs[k]!)) &&
    allLt 8 (fun k => allLt 8 fun l => isOneOrZ (compA 2300 (compA 2300 (compA 2300 qArrs[k]!
      qArrs[l]!) (invCand 2300 qArrs[k]!)) (invCand 2300 qArrs[l]!))) &&
    allLt 2 (fun i => allLt 8 fun l => decide (qCol W i l < 256) &&
      isProdOrZ (compA 2300 (compA 2300 cArrs[i]! qArrs[l]!) (invCand 2300 cArrs[i]!))
        (qCol W i l)) && qCol W 0 0 == 143 &&
    allLt 255 (fun v => spanIter (qActCols W 0) (qActCols W 1) 8 (spanIns 1 (v + 1)) ==
      2 ^ 256 - 1) &&
    allLt 256 (fun a => decide (thetaN W a < 256) && (thetaN W a != 0 || a == 0 || a == 218)) &&
    thetaN W 218 == 0

end CFSG.Sporadic.Co2Schreier
