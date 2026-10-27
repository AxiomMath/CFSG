module

public import CFSG.Permutation.FiveTransitive.PGroupFixedInvolution
public import CFSG.Permutation.FiveTransitive.MaximalInvolutionFixedSet

public section

namespace CFSG

namespace FiveTransitive.BoundedInvolutionFixedSet

open MulAction

theorem exact_and_semiregular
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (k : ℕ) (hmax : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ k)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hlarge : k ≤ Nat.card (fixedPoints Q X)) :
    Nat.card (fixedPoints Q X) = k ∧
      (∀ t : G, t ∈ Q → orderOf t = 2 → fixedBy X t = fixedPoints Q X) ∧
      (∃ t : G, t ∈ Q ∧ orderOf t = 2 ∧ fixedBy X t = fixedPoints Q X ∧
        (fixedBy X t).ncard = k ∧
        ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ (fixedBy X t).ncard) ∧
      ∀ q : G, q ∈ Q → q ≠ 1 → ∀ x : X, x ∉ fixedPoints Q X → q • x ≠ x := by
  obtain ⟨t, htQ, ht, hsub, hcard⟩ := PGroupFixedInvolution.exists_involution (X := X) Q hQ hne
  have hc : Nat.card (fixedPoints Q X) = k := by have := hmax t ht; omega
  have hall : ∀ u : G, u ∈ Q → orderOf u = 2 → fixedBy X u = fixedPoints Q X := by
    intro u hu hu2
    apply (Set.eq_of_subset_of_ncard_le (fun x hx => mem_fixedPoints.mp hx ⟨u, hu⟩) ?_).symm
    have hc' : (fixedPoints Q X).ncard = k := by simpa only [Nat.card_coe_set_eq] using hc
    rw [hc']
    exact hmax u hu2
  have hteq := hall t htQ ht
  have htc : (fixedBy X t).ncard = k := by rw [hteq, ←Nat.card_coe_set_eq, hc]
  have htmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ (fixedBy X t).ncard := by
    rw [htc]
    exact hmax
  refine ⟨hc, hall, ⟨t, htQ, ht, hteq, htc, htmax⟩, ?_⟩
  intro q hq hqne x hx hqx
  have he := MaximalInvolutionFixedSet.eq_one_of_fixing_outside G X t htmax Q hQ
    (by intro u y hy; rw [hteq] at hy; exact mem_fixedPoints.mp hy u)
    ⟨q, hq⟩ x (by rwa [hteq]) hqx
  exact hqne (congrArg Subtype.val he)

end FiveTransitive.BoundedInvolutionFixedSet

end CFSG
