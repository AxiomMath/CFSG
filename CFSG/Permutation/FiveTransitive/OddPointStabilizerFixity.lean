module

public import CFSG.Permutation.FiveTransitive.PGroupFixedInvolution

public section

namespace CFSG

namespace FiveTransitive.OddPointStabilizerFixity

open MulAction

theorem odd_fixed_card
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (S : Subgroup G) (hS : IsPGroup 2 S) (hodd : Odd (Nat.card X)) :
    Odd (Nat.card (fixedPoints S X)) := by
  have hp := hS.card_modEq_card_fixedPoints X
  change Nat.card X % 2 = Nat.card (fixedPoints S X) % 2 at hp
  rw [Nat.odd_iff] at hodd ⊢
  exact hp.symm.trans hodd

end FiveTransitive.OddPointStabilizerFixity

end CFSG
