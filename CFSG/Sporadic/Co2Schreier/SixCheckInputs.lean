module

public import CFSG.Sporadic.Co2Schreier.WitCheck
public import CFSG.Sporadic.Co2Schreier.ChainCheck
public import CFSG.Sporadic.Co2Schreier.Lin
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.ChainCheck
public meta import CFSG.Sporadic.Co2Schreier.Lin
public meta import CFSG.Sporadic.Co2Schreier.Chains
public import CFSG.Sporadic.Co2Schreier.Chains

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Cert
  CFSG.Monster.B.Mathieu

@[expose] def sixIdx (k : ℕ) : ℕ := witRec.wLocal.sixBasisIndices.getD k 0

@[expose] def sixAnchorIdx : ℕ := witRec.wLocal.sixAnchor

@[expose] def sixPacked : Array ℕ :=
  (Array.range 6).map fun k => co2PackedVecs[sixIdx k]! ^^^ co2PackedVecs[sixAnchorIdx]!

@[expose] def colBits (rows : List ℕ) (k : ℕ) : ℕ :=
  (List.range 6).foldl (fun acc j => if (rows.getD j 0).testBit k then acc ||| (1 <<< j) else acc)
    0

@[expose] def colsOf (rows : List ℕ) : Array ℕ := (Array.range 6).map (colBits rows)

@[expose] def colMul (rows : List ℕ) (x : ℕ) : ℕ := xorBits (colsOf rows) x

@[expose] def sixImage (g : Array ℕ) (k : ℕ) : ℕ :=
  co2PackedVecs[g[sixIdx k]!]! ^^^ co2PackedVecs[g[sixAnchorIdx]!]!

@[expose] def sixCheck (W : WitCert) : Bool :=
  sixPacked.size == 6 && allLt 6 (fun k => decide (sixPacked[k]! < 2 ^ 22)) &&
    allLt 64 (fun m => m == 0 || xorBits sixPacked m != 0) &&
    allLt 6 (fun k => decide (sixIdx k < 2300)) && decide (sixAnchorIdx < 2300) &&
    allLt 2 (fun i => allLt 6 fun k =>
      sixImage cArrs[i]! k == xorBits sixPacked (colBits (W.wLocal.sixRows.getD i []) k)) &&
    allLt 8 (fun m => allLt 6 fun k => sixImage qArrs[m]! k == sixPacked[k]!) &&
    recordOK 63 W.wLocal.sixActionChain 4 &&
    recordOrbits 63 W.wLocal.sixActionChain == [63, 32, 15, 8, 3, 2] &&
    allLt 2 (fun i => allLt 63 fun p =>
      (W.wLocal.sixActionChain.origArrs[i]!)[p]! + 1 ==
        colMul (W.wLocal.sixRows.getD i []) (p + 1))

end CFSG.Sporadic.Co2Schreier
