module

public import CFSG.Permutation.FiveTransitive.SemiregularCentralizerBound
public import CFSG.Permutation.FiveTransitive.HigherTwoCycleShape

public section

namespace CFSG

namespace FiveTransitive.FourCentralizerFixedPointFree

open MulAction Equiv CyclePatternRoots

theorem fixed_ncard_zero
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hcard : Nat.card Q = 4)
    (hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1)
    (a : G) (hcentral : ∀ q : Q, a * (q : G) = (q : G) * a)
    (hsmall : (fixedBy X a).ncard < 4)
    (hzero : (fixedBy X a ∩ fixedPoints Q X).ncard = 0) :
    (fixedBy X a).ncard = 0 := by
  by_contra hn
  obtain ⟨x, hx⟩ := (Set.ncard_pos (Set.toFinite _)).mp (Nat.pos_of_ne_zero hn)
  have hxF : x ∉ fixedPoints Q X := by
    intro h
    have he : fixedBy X a ∩ fixedPoints Q X = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp hzero
    have hm : x ∈ fixedBy X a ∩ fixedPoints Q X := ⟨hx, h⟩
    rw [he] at hm
    exact hm
  have hbound := SemiregularCentralizerBound.card_le_fixed_diff_of_centralizing G X Q a x hx hxF
    (fun q => hfree q x hxF) hcentral
  have hle : (fixedBy X a \ fixedPoints Q X).ncard ≤ (fixedBy X a).ncard :=
    Set.ncard_le_ncard Set.sdiff_subset
  omega

theorem square_fixed_two
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hlocal : SixLocalSylowExponentTwo.EvenSixLocal G X)
    (hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (toPerm u : Perm X)) = 2 ∨
      Nat.card (Function.fixedPoints (toPerm u : Perm X)) = 6)
    (a : G) (ha : orderOf a = 4)
    (hzero : Nat.card (Function.fixedPoints (toPerm a : Perm X)) = 0) :
    Nat.card (Function.fixedPoints (toPerm (a ^ 2) : Perm X)) = 2 := by
  have hfour : 0 < Nat.card (FourRoot (toPerm a : Perm X)) := by
    apply TwoPowerPeriodWitness.four_card_pos_of_order_four
    rw [HigherTwoCycleShape.order_toPerm, ha]
  have hshape := LocalEvenCycleShape.two_power_shape hlocal (fun u hu => by rcases hinv u hu with h | h <;> omega)
    a 2 (by decide) ha hfour
  have ha2 : orderOf (a ^ 2) = 2 := by rw [orderOf_pow, ha]; norm_num
  have hinv2 := hinv (a ^ 2) ha2
  have hsum := TwoElementFixedBound.fixed_square_card (toPerm a : Perm X)
  have hpow : (toPerm a : Perm X) ^ 2 = (toPerm (a ^ 2) : Perm X) := by
    exact (map_pow (toPermHom G X) a 2).symm
  rw [hzero, hpow] at hsum
  omega

end FiveTransitive.FourCentralizerFixedPointFree

end CFSG
