module

public import CFSG.CGT.T75JM.L2FInputs
import Certificates.Kernel.T75JM.N0KGlue
import Certificates.Kernel.T75JM.L2KChecks
import Certificates.Kernel.T75JM.L2KFChecks
import CFSG.Certificates.Kernel.T75JM.L2KFSound
public import CFSG.CGT.T75JM.PData

public section

open CFSG.CGT.T75JM CFSG.KC.N0K

namespace Certificates

open CFSG.CosetTable CFSG.CGT.T75JM in
theorem certificate271031 : (dMemCheck = true) ∧ (dRelCheck = true) ∧ (abWordsCheck = true) ∧
    (∀ z : PG 6 rels6, (∀ i : Fin 2, z * val6 (bGen i) * z⁻¹ ∈
        ({1, val6 (bGen 0), val6 (bGen 1), val6 (bGen 0) * val6 (bGen 1)} : Set _)) →
      (∀ i : Fin 2, z * val6 (dGen i) = val6 (dGen i) * z) → z = 1) ∧
    (thetaSqCheck = true) ∧
    (∀ u : Fin 2 → PG 6 rels6,
      (∀ i : Fin 2, ∀ p : Fin 2,
        u i * val6 (bGen p) * (u i)⁻¹ ∈
          ({1, val6 (bGen 0), val6 (bGen 1), val6 (bGen 0) * val6 (bGen 1)} : Set _) ∧
        (u i)⁻¹ * val6 (bGen p) * u i ∈
          ({1, val6 (bGen 0), val6 (bGen 1), val6 (bGen 0) * val6 (bGen 1)} : Set _)) →
      (([0, 0, 0, 0] : List (Fin 2)).map u).prod = 1 →
      (([1, 1, 1, 1] : List (Fin 2)).map u).prod = 1 →
      (([0, 1, 0, 1, 0, 1] : List (Fin 2)).map u).prod = 1 →
      (∀ w ∈ aWords, (w.map u).prod ∈
          ({1, val6 (bGen 0), val6 (bGen 1), val6 (bGen 0) * val6 (bGen 1)} : Set _) ∧
        (w.map u).prod ≠ 1) →
      (∀ w ∈ bWords, (∃ k < 16, (w.map u).prod = val6 (CFSG.CGT.T75JM.tw k)) ∧ (w.map u).prod ≠ 1) →
      ∃ j : PG 6 rels6,
        (∀ p : Fin 2,
          j * val6 (bGen p) * j⁻¹ ∈
            ({1, val6 (bGen 0), val6 (bGen 1), val6 (bGen 0) * val6 (bGen 1)} : Set _) ∧
          j⁻¹ * val6 (bGen p) * j ∈
            ({1, val6 (bGen 0), val6 (bGen 1), val6 (bGen 0) * val6 (bGen 1)} : Set _)) ∧
        ∀ i : Fin 2, j * u i * j⁻¹ = val6 (dTheta i)) := by
  refine ⟨dMemCheck_of letterRd_LP dMemK_ok, dRelCheck_of letterRd_LP dRelK_ok,
    abCheck_of letterRd_LP abK_ok, fun z hz hd => ?_, thSqCheck_of letterRd_LP thSqK_ok,
    fun u hD r1 r2 r3 hA hB => ?_⟩
  · refine center_of letterRd_LP n0Inv_ok n0k_ok centerK_ok z (fun i => ?_) hd
    have e := hz i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at e
    exact e
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD hA
    obtain ⟨j, hj, hji⟩ := swap_of letterRd_LP n0Inv_ok n0k_ok swK_ok u
      (fun i => ⟨(hD i 0).1, (hD i 1).1, (hD i 0).2, (hD i 1).2⟩) r1 r2 r3 hA hB
    obtain ⟨j0, j1, j2, j3⟩ := hj
    refine ⟨j, fun p => ?_, hji⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    fin_cases p
    · exact ⟨j0, j2⟩
    · exact ⟨j1, j3⟩

end Certificates
