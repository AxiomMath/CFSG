module

public import CFSG.Permutation.FiveTransitive.SixteenOrbitLocalization

public section

namespace CFSG

namespace FiveTransitive.SemiregularFixedDegree

open MulAction

theorem card_add_fixed_le (G X : Type*) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (S : Subgroup G) [Nontrivial S]
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1) :
    Nat.card S + (fixedPoints S X).ncard ≤ Nat.card X := by
  classical
  have hex : ∃ x : X, x ∉ fixedPoints S X := by
    by_contra hn
    push Not at hn
    obtain ⟨q,hq⟩ := exists_ne (1 : S)
    apply hq
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro x
    simpa only [one_smul] using mem_fixedPoints.mp (hn x) q
  obtain ⟨x,hx⟩ := hex
  have ho : (orbit S x).ncard = Nat.card S :=
    SixteenOrbitLocalization.orbit_card_of_free S x (fun q => hfree q x hx)
  have hd : Disjoint (orbit S x) (fixedPoints S X) := by
    rw [Set.disjoint_left]
    intro y hy hf
    exact SemiregularNormalizerBound.orbit_not_fixed S X x hx hy hf
  have h := Set.ncard_le_ncard (Set.subset_univ (orbit S x ∪ fixedPoints S X))
  rwa [Set.ncard_union_eq hd,ho,Set.ncard_univ] at h

end FiveTransitive.SemiregularFixedDegree

end CFSG
