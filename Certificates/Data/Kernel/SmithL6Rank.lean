module

public import Certificates.Data.SmithL6RhoCheck

public section

namespace CFSG.SmithL6.Kernel

open CFSG.SmithL6
open CFSG.SmithE (applyCols)

@[expose] def annK (i : Nat) : Nat := let W := wB i; annMaskOf W.1 W.2.1 W.2.2

@[expose] def countMN (M N : Nat) : Nat :=
  tvList.toList.countP fun p => M.testBit p.1 && N.testBit p.2

@[expose] def meetCardK (i j : Nat) : Nat := countMN (wMask i &&& wMask j) (annK i &&& annK j)

@[expose] def distBK (i j : Nat) : Nat :=
  let c := meetCardK i j
  if c == 49 then 0 else if c == 9 then 1 else if c == 1 then 2 else 3

@[expose] def distMat (rr cc : List Nat) : List (List Nat) := rr.map fun i => cc.map fun j => distBK i j

@[expose] def rankOKD (R : Nat) (D : List (List Nat)) (inv : List Nat) : Bool :=
  (List.range 21).all fun s => (List.range 21).all fun u =>
    (List.range 21).foldl (fun acc t => acc ^^ (R.testBit ((D.getD s []).getD t 0) &&
      (inv.getD t 0).testBit u)) false == (s == u)

@[expose] def rankWitK (r : Nat) : Bool :=
  let rr := (rankRows.toList.getD r #[]).toList
  let cc := (rankCols.toList.getD r #[]).toList
  let inv := (rankInv.toList.getD r #[]).toList
  rr.length == 21 && cc.length == 21 && inv.length == 21 && rr.all (· < 1395) &&
    cc.all (· < 1395) && rankOKD (rankRels.toList.getD r 0) (distMat rr cc) inv

@[expose] def chkRankK : Bool :=
  rankRows.toList.length == 6 && rankCols.toList.length == 6 && rankInv.toList.length == 6 &&
    (List.range 6).all rankWitK

@[expose] def chkSpanWK : Bool :=
  spanIdx.toList.length == 20 && spanCoef.toList.length == 20 && spanIdx.toList.all (· < 1395) &&
    (List.range 20).all fun m =>
      applyCols (spanIdx.toList.map wt).toArray (spanCoef.toList.getD m 0) == 2 ^ m

end CFSG.SmithL6.Kernel
