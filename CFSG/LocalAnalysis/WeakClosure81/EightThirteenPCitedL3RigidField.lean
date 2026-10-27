module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityLinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem outerRigid_field_std {k : Type} [Field k] [Finite k] {σ : k ≃+* k} (hk : Nat.card k = 4)
    (hσ : ∀ a, σ a = a ^ 2) {γ : MulAut (projectiveSL 3 k)} (hγ : γ * γ = 1)
    (hc : γ * (fieldAut 3 k σ) = (fieldAut 3 k σ) * γ)
    (hf : ∀ x : projectiveSL 3 k, (fieldAut 3 k σ) x = x → γ x = x) :
    γ = 1 ∨ γ = fieldAut 3 k σ := by
  obtain ⟨-, -, hNinn, -, hNC, -, hCN⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.linear_quadratic_field_full_centralizer_rigidity
      (K := k) (n := 3) σ (by norm_num)
  have hγcent : γ ∈ Subgroup.centralizer
      ((CFSG.ComponentClassification.UnbalancedCatalog.subfieldConj 3 σ).range :
        Set (MulAut (projectiveSL 3 k))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    obtain ⟨g, rfl⟩ := hNinn hn
    have hcτ : fieldAut 3 k σ * MulAut.conj g = MulAut.conj g * fieldAut 3 k σ :=
      Subgroup.mem_centralizer_iff.mp (hNC hn) (fieldAut 3 k σ) (Set.mem_singleton _)
    have hconj : MulAut.conj ((fieldAut 3 k σ) g) = MulAut.conj g := by
      rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv (fieldAut 3 k σ) g, hcτ]
      group
    have hτg : (fieldAut 3 k σ) g = g :=
      (CFSG.RankThree.PartTwo.KFacts.L34.conj_injective hk) hconj
    have hγg : γ g = g := hf g hτg
    have hconjγ : γ * MulAut.conj g * γ⁻¹ = MulAut.conj g := by
      rw [CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv γ g, hγg]
    have hcomm : γ * MulAut.conj g = MulAut.conj g * γ := by
      calc γ * MulAut.conj g = (γ * MulAut.conj g * γ⁻¹) * γ := by group
        _ = MulAut.conj g * γ := by rw [hconjγ]
    exact hcomm.symm
  rw [hCN] at hγcent
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hγcent
  have hτ2 : (fieldAut 3 k σ) ^ (2 : ℕ) = 1 := by
    rw [pow_two]
    exact LinearThreeFourOuter.fieldAut_sigma_mul_self hσ hk
  have hτ2' : (fieldAut 3 k σ) ^ (2 : ℤ) = 1 := by
    simpa using hτ2
  rw [← hm, zpow_eq_zpow_emod (n := (2 : ℤ)) m hτ2']
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left
    rw [h]
    simp
  · right
    rw [h]
    simp

end CFSG.LocalAnalysis.WeakClosure81

end
