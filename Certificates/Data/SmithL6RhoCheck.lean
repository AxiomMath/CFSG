module

public import Certificates.Data.SmithL6Check
public import Certificates.Data.SmithL6RhoData

public section

namespace CFSG.SmithL6

open CFSG.SmithE (applyCols)

@[expose] def chkSpanW : Bool :=
  spanIdx.size == 20 && spanCoef.size == 20 && spanIdx.all (· < 1395) &&
    (List.range 20).all fun m =>
      applyCols (spanIdx.map fun i => wtArr[i]!) spanCoef[m]! == 2 ^ m

@[expose] def rankOK (R : Nat) (rr cc inv : Array Nat) : Bool :=
  rr.size == 21 && cc.size == 21 && inv.size == 21 && rr.all (· < 1395) && cc.all (· < 1395) &&
    (List.range 21).all fun s => (List.range 21).all fun u =>
      (List.range 21).foldl (fun acc t => acc ^^ (relB R rr[s]! cc[t]! && inv[t]!.testBit u))
        false == (s == u)

@[expose] def chkRank : Bool :=
  rankRels == #[2, 4, 6, 10, 12, 14] && rankRows.size == 6 && rankCols.size == 6 &&
    rankInv.size == 6 &&
    (List.range 6).all fun r => rankOK rankRels[r]! rankRows[r]! rankCols[r]! rankInv[r]!

end CFSG.SmithL6
