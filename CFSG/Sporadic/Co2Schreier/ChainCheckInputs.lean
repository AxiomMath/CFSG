module

public import CFSG.Sporadic.Co2Schreier.Arrays
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu

@[expose] def levelsS : Array Level :=
  rawLevels 2300 localRec.chains.S.strongArrs localRec.chains.S.baseArr

@[expose] def recordOK (n : ℕ) (c : ChainRecord) (chunks : ℕ) : Bool :=
  rawChainOK n c.origArrs c.strongArrs c.baseArr c.wordArrs chunks

@[expose] def recordOrbits (n : ℕ) (c : ChainRecord) : List ℕ :=
  rawOrbitSizes n c.strongArrs c.baseArr

@[expose] def commA (t u : Array ℕ) : Bool := eqA 2300 (compA 2300 t u) (compA 2300 u t)

@[expose] def wordsCheck (L : LocalCert) (lv : Array Level) : Bool :=
  allInv aArrs && allInv cInitArrs && allInv dArrs && allInv dStarArrs && allInv rArrs &&
    allInv cArrs && allInv cStarArrs && allInv qArrs && allInv sArrs &&
    isInvA 2300 wArr (invCand 2300 wArr) && isInvA 2300 hArr (invCand 2300 hArr) &&
    aArrs.size == 2 && cInitArrs.size == 2 && dArrs.size == 2 && dStarArrs.size == 7 &&
    rArrs.size == 10 && cArrs.size == 2 && cStarArrs.size == 9 && qArrs.size == 8 &&
    sArrs.size == 15 &&
    allLt 2 (fun k => eqA 2300 L.chains.C.origArrs[k]! cArrs[k]!) &&
    allLt 2 (fun k => eqA 2300 L.chains.D.origArrs[k]! dArrs[k]!) &&
    allLt 15 (fun k => eqA 2300 L.chains.S.origArrs[k]! sArrs[k]!) &&
    allLt 4 (fun k => eqA 2300 L.chains.join.origArrs[k]! (cArrs ++ dArrs)[k]!) &&
    allLt 8 (fun k => siftA 2300 lv L.chains.S.baseArr 0 qArrs[k]!) &&
    allLt 10 (fun k => siftA 2300 lv L.chains.S.baseArr 0 rArrs[k]!) &&
    siftA 2300 lv L.chains.S.baseArr 0 zArr && siftA 2300 lv L.chains.S.baseArr 0 tArr &&
    eqA 2300 (compA 2300 zArr zArr) (idA 2300) && eqA 2300 (compA 2300 tArr tArr) (idA 2300) &&
    !eqA 2300 zArr (idA 2300) && !eqA 2300 tArr (idA 2300) &&
    allLt 2 (fun k => commA cArrs[k]! zArr) && allLt 2 (fun k => commA dArrs[k]! tArr)

end CFSG.Sporadic.Co2Schreier
