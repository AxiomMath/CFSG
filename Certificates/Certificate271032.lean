module

public import CFSG.CGT.T75M23.L2FInputs7
public import CFSG.CGT.T75M23.N7Group
import Certificates.Kernel.T75M23.N7KGlue
import Certificates.Kernel.T75M23.L2K7Checks
import Certificates.Kernel.T75M23.L2K7DChecks
import Certificates.Kernel.T75M23.L2K7GChecks
import CFSG.Certificates.Kernel.T75M23.L2K7DSound
import CFSG.Certificates.Kernel.T75M23.L2K7GSound

public section

open CFSG.CGT.T75M23 CFSG.KC.N7K CFSG.KC.TabWord.M23

namespace Certificates

open CFSG.CGT.T75M23 in
theorem certificate271032 : (tCheck7 = true) ∧ (bCheck7 = true) ∧ (normalCheck7 = true) ∧
    (∀ x : N7, x * x = 1 → (∀ k < 16, x ≠ n7 (tw7 k)) → ∃ n : N7, n * n7 (bGen7 0) * n⁻¹ = x) ∧
    (∀ c : N7, c * c = 1 → c * n7 (bGen7 0) = n7 (bGen7 0) * c →
      (∀ k < 16, c ≠ n7 (tw7 k)) → (∀ k < 16, n7 (bGen7 0) * c ≠ n7 (tw7 k)) →
      c ≠ n7 (bGen7 0) →
      (∀ y : N7, (y * n7 (bGen7 0) = n7 (bGen7 0) * y ∨ y * c = c * y ∨
          y * (n7 (bGen7 0) * c) = n7 (bGen7 0) * c * y) →
        y * n7 (bGen7 0) * y⁻¹ ∈ ({1, n7 (bGen7 0), c, n7 (bGen7 0) * c} : Set _) ∧
        y * c * y⁻¹ ∈ ({1, n7 (bGen7 0), c, n7 (bGen7 0) * c} : Set _) ∧
        y⁻¹ * n7 (bGen7 0) * y ∈ ({1, n7 (bGen7 0), c, n7 (bGen7 0) * c} : Set _) ∧
        y⁻¹ * c * y ∈ ({1, n7 (bGen7 0), c, n7 (bGen7 0) * c} : Set _)) →
      ∃ n : N7, n * n7 (bGen7 0) * n⁻¹ ∈ ({1, n7 (bGen7 0), c, n7 (bGen7 0) * c} : Set _) ∧
        n * n7 (bGen7 1) * n⁻¹ ∈ ({1, n7 (bGen7 0), c, n7 (bGen7 0) * c} : Set _)) ∧
    (dMemCheck7 = true) ∧ (dRelCheck7 = true) ∧ (abWordsCheck7 = true) ∧
    (∀ z : N7, (∀ i : Fin 2, z * n7 (bGen7 i) * z⁻¹ ∈
        ({1, n7 (bGen7 0), n7 (bGen7 1), n7 (bGen7 0) * n7 (bGen7 1)} : Set _)) →
      (∀ i : Fin 3, z * n7 (dGen7 i) = n7 (dGen7 i) * z) → z = 1) ∧
    (thetaSqCheck7 = true) ∧
    (∀ u : Fin 3 → N7,
      (∀ i : Fin 3, ∀ p : Fin 2,
        u i * n7 (bGen7 p) * (u i)⁻¹ ∈
          ({1, n7 (bGen7 0), n7 (bGen7 1), n7 (bGen7 0) * n7 (bGen7 1)} : Set _) ∧
        (u i)⁻¹ * n7 (bGen7 p) * u i ∈
          ({1, n7 (bGen7 0), n7 (bGen7 1), n7 (bGen7 0) * n7 (bGen7 1)} : Set _)) →
      (([0, 0] : List (Fin 3)).map u).prod = 1 →
      (([1, 1] : List (Fin 3)).map u).prod = 1 →
      (([2, 2, 2] : List (Fin 3)).map u).prod = 1 →
      (∀ w ∈ dRels7, (w.map u).prod = 1) →
      (∀ w ∈ aWords7, (w.map u).prod ∈
          ({1, n7 (bGen7 0), n7 (bGen7 1), n7 (bGen7 0) * n7 (bGen7 1)} : Set _) ∧
        (w.map u).prod ≠ 1) →
      (∀ w ∈ bWords7, (∃ k < 16, (w.map u).prod = n7 (tw7 k)) ∧ (w.map u).prod ≠ 1) →
      ∃ j : N7,
        (∀ p : Fin 2,
          j * n7 (bGen7 p) * j⁻¹ ∈
            ({1, n7 (bGen7 0), n7 (bGen7 1), n7 (bGen7 0) * n7 (bGen7 1)} : Set _) ∧
          j⁻¹ * n7 (bGen7 p) * j ∈
            ({1, n7 (bGen7 0), n7 (bGen7 1), n7 (bGen7 0) * n7 (bGen7 1)} : Set _)) ∧
        ∃ k : Fin 2, ∀ i : Fin 3, j * u i * j⁻¹ = n7 (thetaW7 k i)) := by
  have h1 := n7InvCheck_eq_true
  have h2 := n7RelCheck_eq_true
  refine ⟨tCheck7_of letterRd_NL tK_ok, bCheck7_of letterRd_NL bK_ok,
    normalCheck7_of letterRd_NL normalK_ok,
    inv_class_of letterRd_NL h1 h2 n7k_ok icK_ok, fun c hcc hcb hcT hbcT hcb0 hcent => ?_,
    dMemCheck7_of letterRd_NL dMemK_ok, dRelCheck7_of letterRd_NL dRelK_ok,
    abCheck7_of letterRd_NL abK_ok, fun z hz hd => ?_, thSqCheck7_of letterRd_NL thSqK_ok,
    fun u hD q0 q1 q2 hR hA hB => ?_⟩
  · have h := klein7_of letterRd_NL h1 h2 n7k_ok klK7_ok c hcc hcb hcT hbcT hcb0 fun y hy => by
      have e := hcent y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at e
      exact e
    simp only [CFSG.KC.N0K.S4, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact h
  · refine center_of letterRd_NL h1 h2 n7k_ok centerK_ok z (fun i => ?_) hd
    have e := hz i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at e
    exact e
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD hA
    obtain ⟨j, hj, hji⟩ := swap7_cls_of letterRd_NL h1 h2 n7k_ok swPass_ok swConj_ok swRows_ok u
      (fun i => ⟨(hD i 0).1, (hD i 1).1, (hD i 0).2, (hD i 1).2⟩) q0 q1 q2 hR hA hB
    obtain ⟨j0, j1, j2, j3⟩ := hj
    refine ⟨j, fun p => ?_, hji⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    fin_cases p
    · exact ⟨j0, j2⟩
    · exact ⟨j1, j3⟩

end Certificates
