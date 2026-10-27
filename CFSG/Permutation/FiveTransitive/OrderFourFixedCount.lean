module

public import CFSG.Permutation.FiveTransitive.HigherTwoCycleShape

public section

namespace CFSG

namespace FiveTransitive.OrderFourFixedCount

open MulAction Equiv CyclePatternRoots

theorem fixed_two_and_two_root_four
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hlocal : SixLocalSylowExponentTwo.EvenSixLocal G X)
    (hinv : ∀ u : G, orderOf u = 2 → Nat.card (Function.fixedPoints (toPerm u : Perm X)) = 6)
    (a : G) (ha : orderOf a = 4)
    (hsmall : Nat.card (Function.fixedPoints (toPerm a : Perm X)) < 4) :
    Nat.card (Function.fixedPoints (toPerm a : Perm X)) = 2 ∧
      Nat.card (TwoRoot (toPerm a : Perm X)) = 4 := by
  have hfour : 0 < Nat.card (FourRoot (toPerm a : Perm X)) := by
    apply TwoPowerPeriodWitness.four_card_pos_of_order_four
    rw [HigherTwoCycleShape.order_toPerm, ha]
  have hshape := LocalEvenCycleShape.two_power_shape hlocal (fun u hu => (hinv u hu).le)
    a 2 (by decide) ha hfour
  have ha2 : orderOf (a ^ 2) = 2 := by rw [orderOf_pow, ha]; norm_num
  have hsum := TwoElementFixedBound.fixed_square_card (toPerm a : Perm X)
  have hsix := hinv (a ^ 2) ha2
  have hsix' : Nat.card (Function.fixedPoints ((toPerm a : Perm X) ^ 2 : Perm X)) = 6 := by
    simpa only [← toPermHom_apply, map_pow] using hsix
  rw [hsix'] at hsum
  omega

end FiveTransitive.OrderFourFixedCount

end CFSG
