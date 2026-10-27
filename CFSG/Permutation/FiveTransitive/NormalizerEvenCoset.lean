module

public import CFSG.Permutation.FiveTransitive.NormalizerFixedComplement
public import CFSG.Permutation.FiveTransitive.TwoGroupCosetFixedBound
public import CFSG.Permutation.FiveTransitive.EvenInvolutionFixed

public section

namespace CFSG

namespace FiveTransitive.NormalizerEvenCoset

open MulAction NormalizerFixedComplement

theorem fixed_card_eq_two
    {G X : Type*} [Group G] [Fintype X] [DecidableEq X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (x : Normalizer Q)
    (hlocal : (fixedBy X (x : G) ∩ fixedPoints Q X).ncard = 5)
    (q : Inside Q) (hqx : orderOf ((q : Normalizer Q) * x) = 2) :
    Nat.card (fixedBy (Domain (X := X) Q) ((q : Normalizer Q) * x)) = 2 := by
  rw [NormalizerFixedComplement.fixed_card]
  let qQ : Q := ⟨q.val.val, q.property⟩
  have h2 : orderOf ((qQ : G) * (x : G)) = 2 :=
    (Subgroup.orderOf_coe ((q : Normalizer Q) * x)).trans hqx
  have hloc : (fixedBy X ((qQ : G) * (x : G)) ∩ fixedPoints Q X).ncard = 5 := by
    rw [TwoGroupCosetFixedBound.coset_fixed_inter Q qQ (x : G)]
    exact hlocal
  exact EvenInvolutionFixed.complementary_card_eq_two _ h2 (heven _) hdegree
    (hmax _ h2) (fixedPoints Q X) hloc

end FiveTransitive.NormalizerEvenCoset

end CFSG
