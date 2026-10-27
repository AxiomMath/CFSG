
module

public import CFSG.Sporadic.Schreier.Co3CertBase
import all CFSG.Sporadic.Schreier.Co3CertBase

public import CFSG.Sporadic.Schreier.Co3CertCheck

public noncomputable section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native

theorem co3ChainArrs_inv : ∀ j < co3ChainArrs.size,
    isInvA 276 co3ChainArrs[j]! (rawInvs 276 co3ChainArrs)[j]! = true := by
  intro j hj
  rw [rawInvs, co3_getElem!_map hj]
  rw [co3ChainArrs_size] at hj
  rw [co3ChainArrs_get hj]
  exact co3Layout_check.2.2.2.2.1 j (by omega)

theorem co3CoprimeArrs_inv : ∀ j < co3CoprimeArrs.size,
    isInvA 276 co3CoprimeArrs[j]! (rawInvs 276 co3CoprimeArrs)[j]! = true := by
  intro j hj
  rw [rawInvs, co3_getElem!_map hj]
  rw [co3CoprimeArrs_size] at hj
  rw [co3CoprimeArrs_get hj]
  exact co3Layout_check.2.2.2.2.1 (14 + j) (by omega)

theorem rep_co3StrongPerm
    {j : ℕ} (hj : j < 14) : Rep 276 co3ChainArrs[j]! (co3StrongPerm j) :=
  (rep_permOfArr (co3ChainArrs_inv j (by rw [co3ChainArrs_size]; exact hj))).1

theorem CERT_Co3_quadratic_action_data :
    co3SchemaVersion = 1 ∧ co3GroupName = "Co3" ∧ co3Prime = 2 ∧ co3Dimension = 22 ∧
    co3Monomials.length = 253 ∧
    (∀ i < 22, ∀ j < 22, i ≤ j → co3Monomials[pairIdx22 i j]? = some (i, j)) ∧
    (∀ r < 276, co3FormWord r < 2 ^ 253) ∧
    co3DiffIdx = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 27] ∧
    co3Chain.originalCount = 2 ∧ co3Chain.strongCount = 14 ∧
    co3Chain.base.toList.map Fin.val = [0, 1, 2, 3, 4, 5, 6] ∧
    co3CoprimeChain.originalCount = 2 ∧ co3CoprimeChain.strongCount = 14 ∧
    co3CoprimeChain.base.toList.map Fin.val = [0, 1, 2, 3, 4, 5, 6] ∧
    (∀ j < 14, Rep 276 co3ChainArrs[j]! (co3StrongPerm j)) ∧
    (∀ j < 14, isInvA 276 co3CoprimeArrs[j]! (invCand 276 co3CoprimeArrs[j]!) = true) ∧
    wordsOK 2 14 co3ChainDerivations = true ∧ wordsOK 2 14 co3CoprimeDerivations = true ∧
    co3CoprimeWord = [-1, -2, -2, 1, -1, -2, -1, -2, -2, 1, 2, 2] ∧
    co3C0 = co3GenPerm 0 ∧ co3C1 = co3WordValue⁻¹ * co3GenPerm 1 * co3WordValue ∧
    co3Point = 0 ∧ co3StabIdx = [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] ∧
    co3StabOrbits = [[0], (List.range 275).map (· + 1)] ∧
    (co3Merges.map fun m => (m.1 : ℕ)) = [1] ∧ (co3Merges.map fun m => m.2.length) = [274] ∧
    (∀ m ∈ co3MergeList, m.1 < 2 ∧ m.2.1 < 276 ∧ m.2.2 < 276) := by
  obtain ⟨-, -, -, -, -, -, -, hlt⟩ := co3Layout_check
  refine ⟨rfl, rfl, rfl, rfl, co3Monomials_pairIdx.1, co3Monomials_pairIdx.2, hlt, rfl, rfl,
    co3ChainArrs_size, by decide, rfl, co3CoprimeArrs_size, by decide,
    fun j hj => rep_co3StrongPerm hj, fun j hj => ?_, co3Words_check.1, co3Words_check.2.1, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel⟩
  rw [co3CoprimeArrs_get hj]
  exact co3Layout_check.2.2.2.2.1 (14 + j) (by omega)

end CFSG.Sporadic.Schreier.Co3
