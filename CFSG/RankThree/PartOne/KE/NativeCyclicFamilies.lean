module

public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.NativeCyclicEndpoint

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint.Chevalley

theorem oddEndpoint_E6_of_cyclic {Cond : ℕ → ℕ → ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (p ℓ f : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
      1 ≤ f → Nat.card K = ℓ ^ f → Cond p ℓ f →
      (∀ Q : Subgroup (adjointGroup Tag.E6 K), IsPGroup p Q → IsCyclic Q) ∧
        ∀ x : adjointGroup Tag.E6 K, orderOf x = p → IsCyclic (Subgroup.centralizer {x})) :
    OddEndpoint .E6 Cond := by
  refine oddEndpoint_E6_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  obtain ⟨hcyc, hcent⟩ := h K p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_of_cyclic_centralizers .E6 (Or.inl rfl) K hp hp3 hcyc hcent

theorem oddEndpoint_E7_of_cyclic {Cond : ℕ → ℕ → ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (p ℓ f : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
      1 ≤ f → Nat.card K = ℓ ^ f → Cond p ℓ f →
      (∀ Q : Subgroup (adjointGroup Tag.E7 K), IsPGroup p Q → IsCyclic Q) ∧
        ∀ x : adjointGroup Tag.E7 K, orderOf x = p → IsCyclic (Subgroup.centralizer {x})) :
    OddEndpoint .E7 Cond := by
  refine oddEndpoint_E7_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  obtain ⟨hcyc, hcent⟩ := h K p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_of_cyclic_centralizers .E7 (Or.inr (Or.inl rfl)) K hp hp3 hcyc hcent

theorem oddEndpoint_E8_of_cyclic {Cond : ℕ → ℕ → ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (p ℓ f : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
      1 ≤ f → Nat.card K = ℓ ^ f → Cond p ℓ f →
      (∀ Q : Subgroup (adjointGroup Tag.E8 K), IsPGroup p Q → IsCyclic Q) ∧
        ∀ x : adjointGroup Tag.E8 K, orderOf x = p → IsCyclic (Subgroup.centralizer {x})) :
    OddEndpoint .E8 Cond := by
  refine oddEndpoint_E8_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  obtain ⟨hcyc, hcent⟩ := h K p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_of_cyclic_centralizers .E8 (Or.inr (Or.inr rfl)) K hp hp3 hcyc hcent

end CFSG.RankThree.PartOne.KE
