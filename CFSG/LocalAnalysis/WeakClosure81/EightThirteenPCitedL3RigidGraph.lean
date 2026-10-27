module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityPureGraph

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog

theorem outerRigid_graph_std {k : Type} [Field k] [Finite k] {σ : k ≃+* k} (hk : Nat.card k = 4)
    (hσ : ∀ a, σ a = a ^ 2) {γ : MulAut (projectiveSL 3 k)} (hγ : γ * γ = 1)
    (hc : γ * (dualAut 3 k) = (dualAut 3 k) * γ)
    (hf : ∀ x : projectiveSL 3 k, (dualAut 3 k) x = x → γ x = x) :
    γ = 1 ∨ γ = dualAut 3 k := by
  have hK : Nat.card k = 2 ^ 2 := by rw [hk]; norm_num
  have hbig :=
    even_linear_canonical_graph_symplectic_centralizers
      (K := k) (n := 3) (f := 2) (by norm_num) hK (le_refl 3)
      (1 : GL (Fin 3) k) (Or.inl rfl)
  set δ : MulAut (projectiveSL 3 k) := dualAut 3 k with hδ
  set N : Subgroup (MulAut (projectiveSL 3 k)) :=
    (FourGroupEvenCanonical.matrixIsometryGroup
      ((1 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)).map (conjAut 3 k) with hN
  obtain ⟨-, hNinn, hβsq, -, hNC, -, h7⟩ := hbig
  have h1 : conjAut 3 k (1 : GL (Fin 3) k) * δ = δ := by rw [map_one, one_mul]
  rw [h1] at hβsq hNC
  have hδ2 : δ ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two]
    exact hβsq
  obtain ⟨hcent, -⟩ := h7 (Or.inr ⟨by simp, by decide⟩)
  rw [h1] at hcent
  have hmem : γ ∈ Subgroup.centralizer ({δ} : Set (MulAut (projectiveSL 3 k))) ⊓
      Subgroup.centralizer (N : Set (MulAut (projectiveSL 3 k))) := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hc.symm
    · exact Subgroup.mem_centralizer_iff.mpr fun n hn => by
        have hδn : δ * n = n * δ :=
          (Subgroup.mem_centralizer_iff.mp (hNC hn)) δ (Set.mem_singleton δ)
        obtain ⟨g, rfl⟩ := hNinn hn
        have hconj : MulAut.conj (δ g) = MulAut.conj g := by
          rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, hδn]
          group
        have hδg : δ g = g := CFSG.RankThree.PartTwo.KFacts.L34.conj_injective hk hconj
        have hγg : γ g = g := hf g hδg
        have hconjγ : γ * MulAut.conj g * γ⁻¹ = MulAut.conj g := by
          rw [CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, hγg]
        have hcomm : MulAut.conj g * γ = γ * MulAut.conj g := by
          conv_lhs => rw [← hconjγ]
          group
        exact hcomm
  rw [hcent] at hmem
  rw [Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨m, hm⟩ := hmem
  rw [← hm]
  rcases Int.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    rw [show m = 2 * j from by rw [two_mul]; exact hj, zpow_mul δ 2 j, hδ2, one_zpow]
  · right
    rw [hj, zpow_add δ (2 * j) 1, zpow_mul δ 2 j, hδ2, one_zpow, one_mul, zpow_one]

end CFSG.LocalAnalysis.WeakClosure81

end
