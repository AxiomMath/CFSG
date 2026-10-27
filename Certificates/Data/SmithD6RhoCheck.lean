module

public import Certificates.Data.SmithD6Check
public import Certificates.Data.SmithD6RhoData

public noncomputable section

namespace CFSG.SmithD6

@[expose] def meetCnt (i j : Nat) : Nat :=
  ((List.range 64).filter fun d => memR pbArr[j]! ppArr[j]! (xorComb pbArr[i]! d)).length

@[expose] def distD (i j : Nat) : Nat :=
  let c := meetCnt i j
  if c == 1 then 3 else if c == 4 then 2 else if c == 16 then 1 else 0

@[expose] def relD (R i j : Nat) : Bool := R.testBit (distD i j)

@[expose] def chkSpanW : Bool :=
  spanIdx.size == 32 && spanCoef.size == 32 && spanIdx.all (· < 75735) &&
    (List.range 32).all fun m =>
      applyCols (spanIdx.map fun i => wtArr[i]!) spanCoef[m]! == 2 ^ m

@[expose] def rankOK (R : Nat) (rr cc inv : Array Nat) : Bool :=
  rr.size == 33 && cc.size == 33 && inv.size == 33 && rr.all (· < 75735) &&
    cc.all (· < 75735) &&
    ((fun A : Array (Array Bool) =>
      (List.range 33).all fun s => (List.range 33).all fun u =>
        (List.range 33).foldl (fun acc t => acc ^^ (A[s]![t]! && inv[t]!.testBit u)) false ==
          (s == u)) (rr.map fun i => cc.map fun j => relD R i j))

@[expose] def chkRank : Bool :=
  rankRels == #[2, 4, 6, 10, 12, 14] && rankRows.size == 6 && rankCols.size == 6 &&
    rankInv.size == 6 &&
    (List.range 6).all fun r => rankOK rankRels[r]! rankRows[r]! rankCols[r]! rankInv[r]!

end CFSG.SmithD6
