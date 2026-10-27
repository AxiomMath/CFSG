module

public import CFSG.Permutation.FiveTransitive.PGroupFixedPrimeElement
public import CFSG.Permutation.FiveTransitive.SetwiseSylowNormalizer

public section

namespace CFSG

namespace FiveTransitive.SetwiseCommutingInvolution

open MulAction

theorem exists_fixing
    (G X : Type*) [Group G] [Finite G] [MulAction G X]
    (s : Set X) (heven : Even (Nat.card (fixingSubgroup G s)))
    (K : Subgroup G) (hK : IsPGroup 2 K)
    (hpreserves : ∀ k : G, k ∈ K → ∀ x ∈ s, k • x ∈ s) :
    ∃ b : G, b ∈ fixingSubgroup G s ∧ orderOf b = 2 ∧
      (∀ x ∈ s, b • x = x) ∧ ∀ k : G, k ∈ K → Commute b k := by
  have hnorm : K ≤ Subgroup.normalizer (fixingSubgroup G s : Set G) := by
    intro k hk
    apply SetwiseSylowNormalizer.normalizes_fixer s k
    intro x
    constructor
    · exact hpreserves k hk x
    · intro hx
      have hh := hpreserves k⁻¹ (K.inv_mem hk) (k • x) hx
      simpa only [inv_smul_smul] using hh
  obtain ⟨b,hb,horder,hcomm⟩ := PGroupFixedPrimeElement.exists_commuting_involution
    G (fixingSubgroup G s) K heven hK hnorm
  exact ⟨b,hb,horder,(mem_fixingSubgroup_iff G).mp hb,hcomm⟩

end FiveTransitive.SetwiseCommutingInvolution

end CFSG
