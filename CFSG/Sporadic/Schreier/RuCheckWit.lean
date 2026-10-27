module

public import CFSG.Sporadic.Schreier.RuWitArrays
public meta import CFSG.Sporadic.Schreier.RuWitArrays
public import Certificates.Certificate2260
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuEnum
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native

theorem ruWit_check :
    ruMRunA.2.2 = true ∧ isInvA 4060 ruM1A (ruInv ruM1A) = true ∧
    isInvA 4060 ruM2A (ruInv ruM2A) = true ∧ isInvA 4060 ruWwA (ruInv ruWwA) = true ∧
    isInvA 4060 ruHwA (ruInv ruHwA) = true ∧
    (∀ i < 3, isInvA 4060 ruLGensA[i]! (ruInv ruLGensA[i]!) = true) ∧
    (∀ i ∈ [1, 2, 3], isInvA 4060 (ruFusGA i) (ruInv (ruFusGA i)) = true) ∧
    lettersOK 2 ruRMWord = true ∧ lettersOK 2 ruAlignmentSeedWord = true ∧
    ruLMWords.all (lettersOK 2) = true ∧
    (∀ i ∈ [1, 2, 3], lettersOK 4 (ruFusRec i).1 = true ∧ lettersOK 2 (ruFusRec i).2.1 = true) ∧
    (∀ p ∈ [5, 7, 13], lettersOK 3 (ruObsRec p).1 = true) ∧
    ruSylowFusion.map (fun r => r.2.2) = [7, 5, 7] ∧
    ruOddNormalObstructions.map (fun r => r.1) = [5, 7, 13] ∧
    ruOddNormalObstructions.map (fun r => r.2.2) = [3, 3, 3] :=
  Certificates.certificate2260

end CFSG.Sporadic.RuSchreier
