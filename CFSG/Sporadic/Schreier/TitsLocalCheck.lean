module

public import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public import Certificates.Certificate2268

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem titsLocalData_check :
    titsFlagArrs.size = 4 ∧ titsAStarArrs.size = 4 ∧ titsDFlagStored.size = 2 ∧
    titsDStarStored.size = 2 ∧ titsHArrs.size = 9 ∧ titsSArrs.size = 9 ∧ titsNArrs.size = 10 ∧
    titsJArrs.size = 9 ∧ titsKArrs.size = 7 ∧ titsRArrs.size = 8 ∧
    allPermsOK 8775 titsFlagArrs = true ∧ allPermsOK 2925 titsAStarArrs = true ∧
    allPermsOK 8775 titsDFlagStored = true ∧ allPermsOK 2925 titsDStarStored = true ∧
    allPermsOK 1755 titsHArrs = true ∧ allPermsOK 1755 titsSArrs = true ∧
    allPermsOK 1755 titsNArrs = true ∧ allPermsOK 1755 titsJArrs = true ∧
    allPermsOK 1755 titsKArrs = true ∧ allPermsOK 1755 titsRArrs = true ∧
    allLt 8775 (fun j => decide (titsBetaArr[j]! < 1755)) = true ∧
    allLt 8775 (fun j => decide (titsKappaArr[j]! < 2925)) = true ∧
    titsLocalWords.all (fun ws => ws.all (lettersOK 13)) = true ∧
    lettersOK 13 titsCenterWord = true ∧ lettersOK 13 titsXWord = true ∧
    lettersOK 13 titsYWord = true ∧
    (titsProvenance.all fun p => lettersOK 13 p.2.2) = true ∧
    (∀ j < 2, lettersOK 4 (titsU j) = true ∧ lettersOK 4 (titsV j) = true) ∧
    titsDerivedDerivations.length = 11 ∧
    (∀ i < 11, lettersOK (2 + i) titsDerivedDerivations[i]! = true) :=
  Certificates.certificate2268.1

theorem titsLocalChains_check :
    rawChainOK 1755 (titsHArrs.extract 0 3) titsHArrs (baseArr 1755 titsHBase)
      (wordsArr 3 9 titsHDerivations) 4 = true ∧
    rawChainOK 1755 (titsSArrs.extract 0 3) titsSArrs (baseArr 1755 titsSBase)
      (wordsArr 3 9 titsSDerivations) 4 = true ∧
    rawChainOK 1755 (titsNArrs.extract 0 4) titsNArrs (baseArr 1755 titsNBase)
      (wordsArr 4 10 titsNDerivations) 4 = true ∧
    rawChainOK 1755 (titsJArrs.extract 0 4) titsJArrs (baseArr 1755 titsJBase)
      (wordsArr 4 9 titsJDerivations) 4 = true ∧
    rawChainOK 1755 (titsKArrs.extract 0 2) titsKArrs (baseArr 1755 titsKBase)
      (wordsArr 2 7 titsKDerivations) 4 = true ∧
    rawChainOK 1755 (titsRArrs.extract 0 3) titsRArrs (baseArr 1755 titsRBase)
      (wordsArr 3 8 titsRDerivations) 4 = true ∧
    rawOrbitSizes 1755 titsHArrs (baseArr 1755 titsHBase) = [10, 8, 8, 8, 2] ∧
    rawOrbitSizes 1755 titsSArrs (baseArr 1755 titsSBase) = [8, 2, 16, 4, 2] ∧
    rawOrbitSizes 1755 titsNArrs (baseArr 1755 titsNBase) = [24, 2, 16, 4, 2] ∧
    rawOrbitSizes 1755 titsJArrs (baseArr 1755 titsJBase) = [2, 2, 64, 2] ∧
    rawOrbitSizes 1755 titsKArrs (baseArr 1755 titsKBase) = [8, 2, 8, 4, 2] ∧
    rawOrbitSizes 1755 titsRArrs (baseArr 1755 titsRBase) = [2, 2, 4, 8, 2] ∧
    titsHWords.length = 3 ∧ titsSWords.length = 3 ∧ titsNWords.length = 4 ∧
    titsJWords.length = 4 ∧ titsKWords.length = 2 ∧ titsRWords.length = 3 ∧
    initialWordsOK titsHArrs titsHWords = true ∧ initialWordsOK titsSArrs titsSWords = true ∧
    initialWordsOK titsNArrs titsNWords = true ∧ initialWordsOK titsJArrs titsJWords = true ∧
    initialWordsOK titsKArrs titsKWords = true ∧ initialWordsOK titsRArrs titsRWords = true :=
  Certificates.certificate2268.2

theorem titsLocalData_letters : (titsLocalWords.all fun ws => ws.all (lettersOK 13)) = true :=
  titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsLocalData_uv : ∀ j < 2, lettersOK 4 (titsU j) = true ∧ lettersOK 4 (titsV j) = true :=
  titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsLocalData_derivLen : titsDerivedDerivations.length = 11 :=
  titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end CFSG.Sporadic.Schreier.Tits
