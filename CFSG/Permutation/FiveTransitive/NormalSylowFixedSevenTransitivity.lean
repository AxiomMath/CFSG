module

public import CFSG.Permutation.FiveTransitive.OddNormalFixerTransitive
public import CFSG.Permutation.FiveTransitive.FixedSevenInternalAction

public section

namespace CFSG

namespace FiveTransitive.NormalSylowFixedSevenTransitivity

open MulAction SubMulAction GenericSylowFixedAction

theorem fixing_pretransitive
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] (hN4 : IsMultiplyPretransitive N X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup N s))
    (hF : Nat.card (sylowFixedPoints N X s S) = 7) :
    IsPretransitive (fixingSubgroup N s) (ofFixingSubgroup N s) := by
  let F := sylowFixedPoints N X s S
  have hpar := fixed_degree_modEq N X s S
  have hnodd : Odd (Nat.card X - s.ncard) := by
    rw [Nat.odd_iff]
    change Nat.card X % 2 = Nat.card F % 2 at hpar
    have hFc : Nat.card F = 7 := hF
    rw [hFc] at hpar
    have hn : 7 ≤ Nat.card X := by
      rw [← hF]
      exact Nat.card_le_card_of_injective (f := fun x : F => x.val) Subtype.val_injective
    rw [hs]
    omega
  let _ : IsMultiplyPretransitive G X 5 := h5
  have htrans : IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) :=
    is_one_pretransitive_iff.mp
      (ofFixingSubgroup.isMultiplyPretransitive G s (by omega : s.ncard + 1 = 5))
  apply OddNormalFixerTransitive.isPretransitive_of_fixed_points G X N s htrans S hnodd
  exact FixedSevenInternalAction.connect_fixed_complement G X h5 N hN4 s hs S hF

end FiveTransitive.NormalSylowFixedSevenTransitivity

end CFSG
