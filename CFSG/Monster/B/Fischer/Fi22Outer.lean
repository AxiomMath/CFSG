
module

public import CFSG.Monster.B.Fischer.Fi22OuterBase
import all CFSG.Monster.B.Fischer.Fi22OuterBase

public import CFSG.Monster.B.Fischer.Fi22OuterCheck
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Fischer

theorem rep_fi22OuterPerm3510 {L : ℕ} (hL : L < 151) :
    Rep 3510 (fi22OuterArr3510 L) (fi22OuterPerm3510 L) :=
  (rep_permOfArr (fi22Outer_check.2.2.2.1 L hL)).1

theorem rep_fi22OuterPerm693 {L : ℕ} (hL : L < 104) :
    Rep 693 (fi22OuterArr693 L) (fi22OuterPerm693 L) :=
  (rep_permOfArr (fi22Outer_check.2.2.2.2.1 L hL)).1

theorem rep_fi22OuterPerm256 {L : ℕ} (hL : L < 16) :
    Rep 256 (fi22OuterArr256 L) (fi22OuterPerm256 L) :=
  (rep_permOfArr (fi22Outer_check.2.2.2.2.2.1 L hL)).1

theorem AT_Fi22_outer_certificate_data :
    (∀ L < 151, Rep 3510 (fi22OuterArr3510 L) (fi22OuterPerm3510 L)) ∧
    (∀ L < 104, Rep 693 (fi22OuterArr693 L) (fi22OuterPerm693 L)) ∧
    (∀ L < 16, Rep 256 (fi22OuterArr256 L) (fi22OuterPerm256 L)) ∧
    fi22OuterChainM.originalCount = 3 ∧ fi22OuterChainM.strongCount = 17 ∧
    fi22OuterChainM.base.toList.map Fin.val = [0, 1, 2, 6, 4, 3] ∧
    fi22OuterChainT.originalCount = 9 ∧ fi22OuterChainT.strongCount = 13 ∧
    fi22OuterChainT.base.toList.map Fin.val = [0, 1, 2, 3, 6, 4] ∧
    fi22OuterChainT256.originalCount = 9 ∧ fi22OuterChainT256.strongCount = 16 ∧
    fi22OuterChainT256.base.toList.map Fin.val = [0, 1, 2, 3] ∧
    fi22OuterChainUnitary.originalCount = 46 ∧ fi22OuterChainUnitary.strongCount = 49 ∧
    fi22OuterChainUnitary.base.toList.map Fin.val = [0, 1, 3, 9, 45] ∧
    fi22OuterChainM693.originalCount = 3 ∧ fi22OuterChainM693.strongCount = 15 ∧
    fi22OuterChainM693.base.toList.map Fin.val = [0, 1, 3, 9, 45] ∧
    fi22OuterChainMComm693.originalCount = 3 ∧ fi22OuterChainMComm693.strongCount = 14 ∧
    fi22OuterChainMComm693.base.toList.map Fin.val = [0, 9, 1, 3, 45] ∧
    fi22OuterChainD693.originalCount = 3 ∧ fi22OuterChainD693.strongCount = 11 ∧
    fi22OuterChainD693.base.toList.map Fin.val = [0, 1, 2, 4] ∧
    wordsOK fi22OuterMGenCount 17 fi22OuterMDerivations = true ∧
    wordsOK fi22OuterTGenCount 13 fi22OuterTDerivations = true ∧
    wordsOK fi22OuterT256GenCount 16 fi22OuterT256Derivations = true ∧
    wordsOK fi22OuterUnitaryGenCount 49 fi22OuterUnitaryDerivations = true ∧
    wordsOK fi22OuterM693GenCount 15 fi22OuterM693Derivations = true ∧
    wordsOK fi22OuterMComm693GenCount 14 fi22OuterMComm693Derivations = true ∧
    wordsOK fi22OuterD693GenCount 11 fi22OuterD693Derivations = true ∧
    fi22OuterI.length = 693 ∧ fi22OuterR.length = 256 ∧
    (∀ x ∈ fi22OuterMPointsNat, x < 3510) ∧ (∀ x ∈ fi22OuterTPointsNat, x < 3510) ∧
    ((List.range 3).map fun r => (fi22OuterWitnessOrbitNat r).length) = [512, 180, 1] ∧
    (∀ r < 3, ∀ x ∈ fi22OuterWitnessOrbitNat r, x < 693) ∧
    fi22OuterWitnessPoints = [0, 9, 270] ∧
    fi22OuterB.length = 693 ∧ fi22OuterV.length = 46 ∧
    (∀ k < 693 * 6, codeAt fi22OuterUnitaryPoints k < 4) ∧
    (∀ k < 46 * 6, codeAt fi22OuterTransvectionVectors k < 4) ∧
    fi22F4 0 = 0 ∧ fi22F4 1 = 1 ∧ fi22F4 2 = F4.ω ∧ fi22F4 3 = 1 + F4.ω ∧
    F4.ω ^ 2 + F4.ω + 1 = 0 ∧
    fi22OuterMCommPairs = [(1, 2), (1, 3), (2, 3)] ∧ fi22OuterCentralWord = [1, 2] ∧
    fi22OuterFixedBounds = [3511, 3511, 3510] ∧
    fi22OuterSourceArtifact = ("blueprint/data/sporadic/fi22-simplicity-certificate.json.gz",
      "f1fe012bdfafe82807a5c76a7a4decfb86f2b269c34ddbb42662493ddb62918d",
      "906e38055bc5d0f5f08be82a4d98fe15cda1695ea088b70201daf5ba3e919dfe") := by
  obtain ⟨-, -, -, -, -, -, hM, hT, hW, hWs, -, -, hU, hV, w1, w2, w3, w4, w5, w6, w7⟩ :=
    fi22Outer_check
  refine ⟨fun L hL => rep_fi22OuterPerm3510 hL, fun L hL => rep_fi22OuterPerm693 hL,
    fun L hL => rep_fi22OuterPerm256 hL, rfl, ?_, ?_, rfl, ?_, ?_, rfl, ?_, ?_, rfl, ?_, ?_, rfl,
    ?_, ?_, rfl, ?_, ?_, rfl, ?_, ?_, w1, w2, w3, w4, w5, w6, w7, ?_, ?_, hM, hT, hWs, hW, rfl,
    ?_, ?_, hU, hV, rfl, rfl, rfl, rfl, by decide, rfl, rfl, rfl, rfl⟩
  · rw [fi22OuterChainM, RawSchreierDatum.ofArrays_strongCount, fi22OuterStrong3510,
      Array.size_ofFn]
    rfl
  · rw [fi22OuterChainM, RawSchreierDatum.ofArrays_base_toList]
    rfl
  · rw [fi22OuterChainT, RawSchreierDatum.ofArrays_strongCount, fi22OuterStrong3510,
      Array.size_ofFn]
    rfl
  · rw [fi22OuterChainT, RawSchreierDatum.ofArrays_base_toList]
    rfl
  · rw [fi22OuterChainT256, RawSchreierDatum.ofArrays_strongCount, fi22OuterStrong256,
      Array.size_ofFn]
  · rw [fi22OuterChainT256, RawSchreierDatum.ofArrays_base_toList]
    rfl
  · rw [fi22OuterChainUnitary, RawSchreierDatum.ofArrays_strongCount, fi22OuterStrong693,
      Array.size_ofFn]
    rfl
  · rw [fi22OuterChainUnitary, RawSchreierDatum.ofArrays_base_toList]
    rfl
  · rw [fi22OuterChainM693, RawSchreierDatum.ofArrays_strongCount, fi22OuterStrong693,
      Array.size_ofFn]
    rfl
  · rw [fi22OuterChainM693, RawSchreierDatum.ofArrays_base_toList]
    rfl
  · rw [fi22OuterChainMComm693, RawSchreierDatum.ofArrays_strongCount, fi22OuterStrong693,
      Array.size_ofFn]
    rfl
  · rw [fi22OuterChainMComm693, RawSchreierDatum.ofArrays_base_toList]
    rfl
  · rw [fi22OuterChainD693, RawSchreierDatum.ofArrays_strongCount, fi22OuterStrong693,
      Array.size_ofFn]
    rfl
  · rw [fi22OuterChainD693, RawSchreierDatum.ofArrays_base_toList]
    rfl
  · simp only [fi22OuterI, fi22FinList, List.length_map, fi22OuterMPointsNat, hex3List,
      List.length_range]
  · simp only [fi22OuterR, fi22FinList, List.length_map, fi22OuterTPointsNat, hex3List,
      List.length_range]
  · simp only [fi22OuterB, List.length_map, List.length_range]
  · simp only [fi22OuterV, List.length_map, List.length_range]

end CFSG.Monster.B.Fischer
