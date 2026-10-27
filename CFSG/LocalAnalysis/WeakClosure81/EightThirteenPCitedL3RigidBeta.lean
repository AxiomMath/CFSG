module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut
import CFSG.RankThree.PartTwo.KFacts.L34Centralizers

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem outerRigid_beta_std {k : Type} [Field k] [Finite k] {σ : k ≃+* k} (hk : Nat.card k = 4)
    (hσ : ∀ a, σ a = a ^ 2) {γ : MulAut (projectiveSL 3 k)} (hγ : γ * γ = 1)
    (hc : γ * (fieldAut 3 k σ * dualAut 3 k) = (fieldAut 3 k σ * dualAut 3 k) * γ)
    (hf : ∀ x : projectiveSL 3 k, (fieldAut 3 k σ * dualAut 3 k) x = x → γ x = x) :
    γ = 1 ∨ γ = fieldAut 3 k σ * dualAut 3 k := by
  have h := CFSG.RankThree.PartTwo.KFacts.L34.unitaryFieldData_of_card hk
  have hσbar : ∀ x, σ x = h.bar x := fun x => by
    rw [hσ, UnitaryFieldData.bar_apply, pow_one]
  obtain ⟨-, -, hNinn, -, hNC, -, hCent7⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.linear_graph_field_full_centralizer_rigidity
      h (n := 3) le_rfl σ hσbar
  have hmem : γ ∈ Subgroup.centralizer
      (((CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 k 3).map (conjAut 3 k) :
        Subgroup (MulAut (projectiveSL 3 k))) : Set (MulAut (projectiveSL 3 k))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    obtain ⟨x, rfl⟩ := hNinn hn
    have hcx : MulAut.conj x ∈ Subgroup.centralizer
        ({fieldAut 3 k σ * dualAut 3 k} : Set (MulAut (projectiveSL 3 k))) := hNC hn
    have h1 : MulAut.conj x * (fieldAut 3 k σ * dualAut 3 k) =
        (fieldAut 3 k σ * dualAut 3 k) * MulAut.conj x :=
      Subgroup.mem_centralizer_singleton_iff.mp hcx
    have hτx : (fieldAut 3 k σ * dualAut 3 k) x = x := by
      apply CFSG.RankThree.PartTwo.KFacts.L34.conj_injective hk
      rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv
        (fieldAut 3 k σ * dualAut 3 k) x, ← h1, mul_inv_cancel_right]
    have hγx : γ x = x := hf x hτx
    have h2 : γ * MulAut.conj x = MulAut.conj x * γ := by
      have h3 := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv γ x
      rw [hγx] at h3
      calc γ * MulAut.conj x = γ * MulAut.conj x * γ⁻¹ * γ := by group
        _ = MulAut.conj x * γ := by rw [h3]
    exact h2.symm
  have hzp : γ ∈ Subgroup.zpowers (fieldAut 3 k σ * dualAut 3 k) := by
    rw [← hCent7]
    exact hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzp
  have hτ2 : (fieldAut 3 k σ * dualAut 3 k) ^ (2 : ℕ) = 1 := by
    rw [pow_two]
    exact CFSG.RankThree.PartTwo.KFacts.L34.betaAut_mul_self (σ := σ) hk hσ
  have hτ2z : (fieldAut 3 k σ * dualAut 3 k) ^ (2 : ℤ) = 1 := by
    simpa using hτ2
  have hred := zpow_eq_zpow_emod (x := fieldAut 3 k σ * dualAut 3 k) m hτ2z
  rcases Int.emod_two_eq_zero_or_one m with h0 | h1
  · left
    rw [← hm, hred, h0, zpow_zero]
  · right
    rw [← hm, hred, h1, zpow_one]

end CFSG.LocalAnalysis.WeakClosure81

end
