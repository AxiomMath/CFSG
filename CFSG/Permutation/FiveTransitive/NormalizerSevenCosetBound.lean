module

public import CFSG.Permutation.FiveTransitive.NormalizerFixedComplement
public import CFSG.Permutation.FiveTransitive.TwoGroupCosetFixedBound

public section

namespace CFSG

namespace FiveTransitive.NormalizerSevenCosetBound

open MulAction NormalizerFixedComplement

theorem coset_fixed_le_two
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hbound : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (x : Normalizer Q) (hx : (x : G) ∈ A) (hxQ : (x : G) ∉ Q)
    (hlocal : (fixedBy X (x : G) ∩ fixedPoints Q X).ncard = 5)
    (q : Inside Q) :
    Nat.card (fixedBy (Domain (X := X) Q) ((q : Normalizer Q) * x)) ≤ 2 := by
  rw [NormalizerFixedComplement.fixed_card]
  let qQ : Q := ⟨q.val.val, q.property⟩
  exact TwoGroupCosetFixedBound.seven_transposition_complement
    hbound Q A hQA hA (x : G) hx hxQ hlocal qQ

end FiveTransitive.NormalizerSevenCosetBound

end CFSG
