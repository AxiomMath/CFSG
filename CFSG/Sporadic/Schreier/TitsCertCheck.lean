module

public import CFSG.Sporadic.Schreier.TitsArrays
public import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs
public import Certificates.Certificate2264

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem titsChains_check :
    titsGenArrs.size = 4 ∧ titsAmbientArrs.size = 14 ∧ titsDerivedArrs.size = 13 ∧
    titsPerfectArrs.size = 12 ∧
    allPermsOK 1755 titsGenArrs = true ∧ allPermsOK 1755 titsAmbientArrs = true ∧
    allPermsOK 1755 titsDerivedArrs = true ∧ allPermsOK 1755 titsPerfectArrs = true ∧
    rawChainOK 1755 (titsAmbientArrs.extract 0 4) titsAmbientArrs (baseArr 1755 titsAmbientBase)
      (wordsArr 4 14 titsAmbientDerivations) 4 = true ∧
    rawChainOK 1755 (titsDerivedArrs.extract 0 2) titsDerivedArrs (baseArr 1755 titsDerivedBase)
      (wordsArr 2 13 titsDerivedDerivations) 4 = true ∧
    rawChainOK 1755 (titsPerfectArrs.extract 0 2) titsPerfectArrs (baseArr 1755 titsPerfectBase)
      (wordsArr 2 12 titsPerfectDerivations) 4 = true ∧
    rawOrbitSizes 1755 titsAmbientArrs (baseArr 1755 titsAmbientBase) = [1755, 80, 8, 2, 4, 4] ∧
    rawOrbitSizes 1755 titsDerivedArrs (baseArr 1755 titsDerivedBase) = [1755, 10, 8, 8, 8, 2] ∧
    rawOrbitSizes 1755 titsPerfectArrs (baseArr 1755 titsPerfectBase) =
      [1755, 10, 8, 2, 8, 4, 2] ∧
    (∀ i < 4, eqA 1755 titsAmbientArrs[i]! titsGenArrs[i]! = true) ∧
    (∀ j < 2, lettersOK 4 (titsU j) = true ∧ lettersOK 4 (titsV j) = true ∧
      isInvA 1755 (wordArr 1755 titsGenArrs (titsU j))
        (invCand 1755 (wordArr 1755 titsGenArrs (titsU j))) = true ∧
      isInvA 1755 (wordArr 1755 titsGenArrs (titsV j))
        (invCand 1755 (wordArr 1755 titsGenArrs (titsV j))) = true ∧
      eqA 1755 titsDerivedArrs[j]! (titsDArr j) = true) ∧
    (∀ j < 2, lettersOK 2 (titsPerfR j) = true ∧ lettersOK 2 (titsPerfS j) = true ∧
      isInvA 1755 (titsDArr j) (invCand 1755 (titsDArr j)) = true ∧
      isInvA 1755 (wordArr 1755 titsDArrs (titsPerfR j))
        (invCand 1755 (wordArr 1755 titsDArrs (titsPerfR j))) = true ∧
      isInvA 1755 (wordArr 1755 titsDArrs (titsPerfS j))
        (invCand 1755 (wordArr 1755 titsDArrs (titsPerfS j))) = true ∧
      eqA 1755 titsPerfectArrs[j]! (titsEArr j) = true) :=
  Certificates.certificate2264

end CFSG.Sporadic.Schreier.Tits
