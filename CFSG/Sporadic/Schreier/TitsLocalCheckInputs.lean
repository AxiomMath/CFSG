module

public import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Sporadic.Schreier.TitsCertCheck

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def titsLocalWords : List (List (List ℤ)) :=
  [titsHWords, titsSWords, titsNWords, titsJWords, titsKWords, titsRWords]

@[expose] def initialWordsOK (A : Array (Array ℕ)) (ws : List (List ℤ)) : Bool :=
  allLt ws.length fun i => lettersOK 13 ws[i]! &&
    eqA 1755 A[i]! (wordArr 1755 titsDerivedArrs ws[i]!)

end CFSG.Sporadic.Schreier.Tits
