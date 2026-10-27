module

public import CFSG.Sporadic.Schreier.RuCheckSylow
public meta import CFSG.Sporadic.Schreier.RuCheckSylow
public import CFSG.Sporadic.Schreier.RuCheckCentersInputs
public import Certificates.Certificate2248

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem ruE_check :
    ruEArr.size = 7 ∧ ruEPar.size = 7 ∧ ruEGen.size = 7 ∧ ruEArr[0]! = ruZA ∧
    (∀ i < 7, isInvA 4060 ruEArr[i]! (invCand 4060 ruEArr[i]!) = true) ∧
    (∀ i, 1 ≤ i → i < 7 → ruEPar[i]! < i ∧ ruEGen[i]! < 2 ∧
      eqA 4060 ruEArr[i]! (ruConjA ruNGensA[ruEGen[i]!]! ruEArr[ruEPar[i]!]!) = true) ∧
    (∀ i < 7, ∀ g < 2, ∃ j < 7, eqA 4060 (ruConjA ruNGensA[g]! ruEArr[i]!) ruEArr[j]! = true) ∧
    (∀ i < 7, ∀ j < 7, i ≠ j → eqA 4060 ruEArr[i]! ruEArr[j]! = false) ∧
    (∀ i < 7, eqA 4060 ruEArr[i]! (idA 4060) = false) ∧
    (∀ i < 7, eqA 4060 (compA 4060 ruEArr[i]! ruEArr[i]!) (idA 4060) = true) ∧
    (∀ i < 7, ∀ j < 7, i ≠ j →
      ∃ k < 7, eqA 4060 (compA 4060 ruEArr[i]! ruEArr[j]!) ruEArr[k]! = true) ∧
    (∀ i < 7, ∀ j < 7, eqA 4060 (compA 4060 ruEArr[i]! ruEArr[j]!)
      (compA 4060 ruEArr[j]! ruEArr[i]!) = true) ∧
    (∀ i < 7, ruSift 4060 (ruField4060 1) ruCBase ruEArr[i]! = true) ∧
    (∀ i < 7, siftA 1920 ruKLevels (ruBaseArr 1920 ruKBase) 0 (ruEF i) = true) ∧
    (∀ i < 7, ∀ k < 8, eqA 4060 (compA 4060 ruEArr[i]! ruKGensA[k]!)
      (compA 4060 ruKGensA[k]! ruEArr[i]!) = true) :=
  Certificates.certificate2248.1

theorem ruZK_check :
    all2 1920 ruKLevels (fun g => !(allLt 8 fun k => ruComm1920 g (ruKF k)) ||
      eqA 1920 g (idA 1920) || (Nat.any 7 fun i _ => eqA 1920 g (ruEF i))) = true :=
  Certificates.certificate2248.2.1

theorem ruCE_check :
    all2 1920 (rawLevels 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase))
      (fun g => !(allLt 7 fun i => ruComm1920 g (ruEF i)) ||
        siftA 1920 ruKLevels (ruBaseArr 1920 ruKBase) 0 g) = true :=
  Certificates.certificate2248.2.2.1

theorem ruCJ_check :
    all2 1920 (rawLevels 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase))
      (fun g => !(allLt 6 fun j => ruComm1920 g (ruJF j)) ||
        siftA 1920 ruJLevels (ruBaseArr 1920 ruJBase) 0 g) = true :=
  Certificates.certificate2248.2.2.2

end CFSG.Sporadic.RuSchreier
