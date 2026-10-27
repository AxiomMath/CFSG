module

public import CFSG.RankThree.PartOne.KE.Endpoint
public import CFSG.RankThree.PartOne.KE.EndpointStatements

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.Chevalley

theorem oddEndpoint_E6_of_native {Cond : ℕ → ℕ → ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (p ℓ f : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
      1 ≤ f → Nat.card K = ℓ ^ f → Cond p ℓ f → PlaneLocalCoreOdd p (adjointGroup Tag.E6 K)) :
    OddEndpoint .E6 Cond := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod.2
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e
    (h K p ℓ f hp hp3 hℓ hℓp hf hK hc)).1

theorem oddEndpoint_E7_of_native {Cond : ℕ → ℕ → ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (p ℓ f : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
      1 ≤ f → Nat.card K = ℓ ^ f → Cond p ℓ f → PlaneLocalCoreOdd p (adjointGroup Tag.E7 K)) :
    OddEndpoint .E7 Cond := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod.2
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e
    (h K p ℓ f hp hp3 hℓ hℓp hf hK hc)).1

theorem oddEndpoint_E8_of_native {Cond : ℕ → ℕ → ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (p ℓ f : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
      1 ≤ f → Nat.card K = ℓ ^ f → Cond p ℓ f → PlaneLocalCoreOdd p (adjointGroup Tag.E8 K)) :
    OddEndpoint .E8 Cond := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod.2
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e
    (h K p ℓ f hp hp3 hℓ hℓp hf hK hc)).1

end CFSG.RankThree.PartOne.KE
