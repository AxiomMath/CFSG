module

public import CFSG.Permutation.FiveTransitive.SetwiseCommutingInvolution
public import CFSG.Permutation.FiveTransitive.FourTransitiveEvenStabilizer

public section

namespace CFSG

namespace FiveTransitive.HighDegreeCommutingInvolution

open MulAction

private theorem exists_of_four_transitive
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : 27 ≤ Fintype.card X) (h4 : IsMultiplyPretransitive G X 4)
    (s : Set X) (hs : s.ncard = 4) (K : Subgroup G) (hK : IsPGroup 2 K)
    (hpreserves : ∀ k : G, k ∈ K → ∀ x ∈ s, k • x ∈ s) :
    ∃ b : G, b ∈ fixingSubgroup G s ∧ orderOf b = 2 ∧
      (∀ x ∈ s, b • x = x) ∧ ∀ k : G, k ∈ K → Commute b k :=
  SetwiseCommutingInvolution.exists_fixing G X s
    (FourTransitiveEvenStabilizer.even_card_fixingSubgroup G X hcard h4 s hs) K hK hpreserves

theorem exists_of_five_transitive
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive G X 5)
    (s : Set X) (hs : s.ncard = 4) (K : Subgroup G) (hK : IsPGroup 2 K)
    (hpreserves : ∀ k : G, k ∈ K → ∀ x ∈ s, k • x ∈ s) :
    ∃ b : G, b ∈ fixingSubgroup G s ∧ orderOf b = 2 ∧
      (∀ x ∈ s, b • x = x) ∧ ∀ k : G, k ∈ K → Commute b k := by
  let _ : IsMultiplyPretransitive G X 5 := h5
  have h4 : IsMultiplyPretransitive G X 4 := isMultiplyPretransitive_of_le
    (G := G) (α := X) (n := 5) (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using (show 5 ≤ Fintype.card X by omega))
  exact exists_of_four_transitive G X (by omega) h4 s hs K hK hpreserves

end FiveTransitive.HighDegreeCommutingInvolution

end CFSG
