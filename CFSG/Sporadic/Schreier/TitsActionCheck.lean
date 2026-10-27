module

public import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public import Certificates.Certificate2262

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem titsLines_check :
    (∀ i < 4, ∀ j < 8775, titsBetaArr[(titsFlagArrs[i]!)[j]!]! =
      (titsGenArrs[i]!)[titsBetaArr[j]!]!) ∧
    (∀ i < 4, ∀ j < 8775, titsKappaArr[(titsFlagArrs[i]!)[j]!]! =
      (titsAStarArrs[i]!)[titsKappaArr[j]!]!) ∧
    (∀ v < 2925, ∀ k < 3, titsLineFlagArr[3 * v + k]! < 8775 ∧
      titsKappaArr[titsLineFlagArr[3 * v + k]!]! = v ∧
      titsBetaArr[titsLineFlagArr[3 * v + k]!]! = titsLinePtArr[3 * v + k]!) ∧
    (∀ v < 2925, titsLinePtArr[3 * v]! < titsLinePtArr[3 * v + 1]! ∧
      titsLinePtArr[3 * v + 1]! < titsLinePtArr[3 * v + 2]! ∧ titsLinePtArr[3 * v + 2]! < 1755) ∧
    (∀ j < 8775, titsLinePos titsKappaArr[j]! titsBetaArr[j]! < 3 ∧
      titsLineFlagArr[3 * titsKappaArr[j]! + titsLinePos titsKappaArr[j]! titsBetaArr[j]!]! = j) ∧
    (((List.range 2925).map titsLineKey).mergeSort fun a b => decide (a ≤ b)).Pairwise
      (· < ·) :=
  Certificates.certificate2262

end CFSG.Sporadic.Schreier.Tits
