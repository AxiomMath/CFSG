module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG

namespace FiveTransitive.SevenFivePermutationSquare

theorem isSwap_and_square
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (h7 : Nat.card Y = 7) (f : Equiv.Perm Y)
    (h5 : Nat.card (Function.fixedPoints f) = 5) :
    f.IsSwap ∧ f ^ 2 = 1 := by
  have hc := f.card_fixedPoints
  rw [f.sum_cycleType, ←Nat.card_eq_fintype_card, h5,
    ←Nat.card_eq_fintype_card, h7] at hc
  have hle := Finset.card_le_univ f.support
  rw [←Nat.card_eq_fintype_card, h7] at hle
  have hs : f.support.card = 2 := by omega
  have hswap := Equiv.Perm.card_support_eq_two.mp hs
  exact ⟨hswap, hswap.orderOf ▸ pow_orderOf_eq_one f⟩

end FiveTransitive.SevenFivePermutationSquare

end CFSG
