module

public import CFSG.Sporadic.Co2Rank3.CheckInputs
public import Certificates.Data.CFSGNative.FischerOddCore.Checks

@[expose] public section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3.Native CFSG.Sporadic.FischerOddCore.Native

def co2Rank3TOK : Bool :=
  let nbr := co2Nbr
  let l0 := p0Rec.1
  let lb := stabRec.1
  let lc := p01Rec.1
  adjOK 2300 co2OrigArrs nbr co2DeltaList &&
    levelIdx co2StrongArrs co2BaseArr 1 == level1Idx &&
    levelIdx co2StrongArrs co2BaseArr 2 == level2Idx &&
    stabWords.all (lettersOK 11) &&
    stabGens.all (fun g => g[0]! == 0 && g[3]! == 3) && stabGens.size == 3 &&
    recOK lev1Gens p0Rec p0Roots && recOK stabGens stabRec stabRoots &&
    recOK lev2Gens p01Rec p01Roots &&
    l0[36]! == 3 && l0[4]! == 3 && l0[5]! == 3 && l0[2]! == 1 && l0[8]! == 1 &&
    listLabelOK 2300 co2DeltaList l0 [3] &&
    listLabelOK 2300 nbr[3]! lb [0, 36, 4, 2] &&
    listLabelOK 2300 nbr[1]! lc [4, 2] &&
    colourLabelOK 2300 (colourT 2300 nbr (idA 2300) (refineBase.take 2) 3) lb
      [0, 1, 2, 3, 4, 5, 36] &&
    boundsOK 2300 nbr (idA 2300) refineBase refineBounds 3 &&
    commonCount nbr[0]! nbr[3]! == 378 && commonCount nbr[0]! nbr[1]! == 324

end CFSG.Sporadic.Co2Rank3
