module

public import CFSG.Sporadic.Schreier.TitsActionCheck
public import CFSG.Sporadic.Schreier.TitsLocalCheck
public import CFSG.Sporadic.Schreier.TitsOrbit
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public import CFSG.Sporadic.Schreier.TitsStabCheckInputs
public import Certificates.Certificate2270

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem titsStab_check :
    (∀ j < 2, isInvA 8775 (wordArr 8775 titsFlagArrs (titsU j))
        (invCand 8775 (wordArr 8775 titsFlagArrs (titsU j))) = true ∧
      isInvA 8775 (wordArr 8775 titsFlagArrs (titsV j))
        (invCand 8775 (wordArr 8775 titsFlagArrs (titsV j))) = true ∧
      isInvA 2925 (wordArr 2925 titsAStarArrs (titsU j))
        (invCand 2925 (wordArr 2925 titsAStarArrs (titsU j))) = true ∧
      isInvA 2925 (wordArr 2925 titsAStarArrs (titsV j))
        (invCand 2925 (wordArr 2925 titsAStarArrs (titsV j))) = true) ∧
    strongOK 8775 2 titsDFlagArrs titsTFlagArrs titsDerivedDerivations = true ∧
    strongOK 2925 2 titsDStarArrs titsTStarArrs titsDerivedDerivations = true ∧
    (∀ j < 2, eqA 8775 titsDFlagArrs[j]! titsDFlagStored[j]! = true ∧
      eqA 2925 titsDStarArrs[j]! titsDStarStored[j]! = true) ∧
    forestOK 8775 titsDFlagArrs #[0] = true ∧ forestOK 2925 titsDStarArrs #[0] = true ∧
    titsHWords.all (fun w => (wordArr 1755 titsDerivedArrs w)[0]! == 0) = true ∧
    titsSWords.all (fun w => (wordArr 8775 titsTFlagArrs w)[0]! == 0) = true ∧
    titsRWords.all (fun w => (wordArr 8775 titsTFlagArrs w)[0]! == 0) = true ∧
    titsNWords.all (fun w => (wordArr 2925 titsTStarArrs w)[0]! == 0) = true ∧
    titsJWords.all (fun w => titsFiveFlags.all fun f => (wordArr 8775 titsTFlagArrs w)[f]! == f) =
      true ∧
    titsKWords.all (fun w => titsThreeFlags.all fun f => (wordArr 8775 titsTFlagArrs w)[f]! == f) =
      true ∧
    titsFiveFlags = [0, 2, 5, 10, 20] ∧ titsThreeFlags = [0, 1, 3] ∧
    allLt 8775 (fun j => (titsBetaArr[j]! == 0) == titsFiveFlags.contains j) = true ∧
    allLt 8775 (fun j => (titsKappaArr[j]! == 0) == titsThreeFlags.contains j) = true ∧
    titsHWords = [[3], [4], [13]] ∧
    powFixes (wordArr 8775 titsTFlagArrs [3]) 4 titsFiveFlags = true ∧
    powFixes (wordArr 8775 titsTFlagArrs [3]) 2 titsFiveFlags = false ∧
    powFixes (wordArr 8775 titsTFlagArrs [3, 4, 13]) 5 titsFiveFlags = true ∧
    powFixes (wordArr 8775 titsTFlagArrs [3, 4, 13]) 1 titsFiveFlags = false ∧
    powFixes (wordArr 8775 titsTFlagArrs titsNWords[2]!) 2 titsThreeFlags = true ∧
    powFixes (wordArr 8775 titsTFlagArrs titsNWords[2]!) 1 titsThreeFlags = false ∧
    powFixes (wordArr 8775 titsTFlagArrs (titsNWords[2]! ++ titsNWords[3]!)) 3 titsThreeFlags =
      true ∧
    powFixes (wordArr 8775 titsTFlagArrs (titsNWords[2]! ++ titsNWords[3]!)) 1 titsThreeFlags =
      false :=
  Certificates.certificate2270

end CFSG.Sporadic.Schreier.Tits
