module

public import CFSG.Sporadic.Schreier.RuTreeEltA
public import CFSG.Sporadic.Schreier.RuWitArrays
public import CFSG.Sporadic.Schreier.RuCheckChains
public import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Schreier.RuTreeEltA
public meta import CFSG.Sporadic.Schreier.RuWitArrays
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuCheckInvInputs
public import Certificates.Certificate2250

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem ruInv_check :
    ruChainOK 4060 (ruField4060 4) 4 6 ruS4060ChainBase ruS4060ChainDerivations = true ∧
    rawOrbitSizes 4060 (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase) = [2048, 8] ∧
    (∀ i < 4, eqA 4060 (ruField4060 4)[i]! ruSGensA[i]! = true) ∧
    count2 4060 ruLevS ruIsInvolA = 687 ∧
    count2 4060 ruLevS (fun t => ruIsInvolA t && ruFixCount t == 92) = 495 ∧
    count2 4060 ruLevS (fun t => ruIsInvolA t && ruFixCount t == 0) = 192 ∧
    all2 4060 ruLevS (fun t => !(ruIsInvolA t && ruFixCount t == 92) || ruZWit t) = true ∧
    (∀ i ∈ [1, 2, 3], count2 4060 ruLevS
      (fun s => eqA 4060 (compA 4060 s (ruFusXA i)) (compA 4060 (ruFusXA i) s)) = 256) ∧
    (∀ i ∈ [1, 2, 3], ∀ j ∈ [1, 2, 3], i < j → all2 4060 ruLevS
      (fun s => !eqA 4060 (compA 4060 s (ruFusXA i)) (compA 4060 (ruFusXA j) s)) = true) ∧
    (∀ i ∈ [1, 2, 3],
      eqA 4060 (compA 4060 (ruFusHA i) ruA0A) (compA 4060 (ruFusXA i) (ruFusHA i)) = true) ∧
    ruFixCount ruA0A = 0 ∧ ruZWit (compA 4060 ruA1A ruA1A) = true ∧
    eqA 4060 (compA 4060 ruA0A ruA0A) (idA 4060) = true ∧ eqA 4060 ruA0A (idA 4060) = false ∧
    eqA 4060 (powA 4060 ruA1A 4) (idA 4060) = true ∧
    eqA 4060 (powA 4060 ruA1A 2) (idA 4060) = false ∧
    eqA 4060 (powA 4060 (compA 4060 ruA0A ruA1A) 13) (idA 4060) = true ∧
    eqA 4060 (powA 4060 ruAB2A 14) (idA 4060) = true ∧
    eqA 4060 (powA 4060 ruAB2A 7) (idA 4060) = false ∧
    eqA 4060 (powA 4060 ruAB2A 2) (idA 4060) = false ∧
    eqA 4060 (powA 4060 (compA 4060 (compA 4060 (compA 4060 ruA0A ruA1A) ruA0A)
      (powA 4060 ruA1A 2)) 29) (idA 4060) = true ∧
    eqA 4060 (compA 4060 ruA0A ruA1A) (compA 4060 ruA1A ruA0A) = false :=
  Certificates.certificate2250

end CFSG.Sporadic.RuSchreier
