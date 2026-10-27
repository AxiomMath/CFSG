module

public import CFSG.Permutation.FiveTransitive.ThirtyTwoTwoGroupCenter
public import CFSG.Permutation.FiveTransitive.ThirtyTwoTwoGroupLargeCenter
public import CFSG.Permutation.FiveTransitive.ThirtyTwoTwoGroupSmallCenter

public section

namespace CFSG

namespace FiveTransitive.ThirtyTwoTwoGroupBound

open MulAction

theorem card_le_thirty_two
    {X : Type*} [Fintype X] [DecidableEq X] (hX : Nat.card X = 32)
    (R : Subgroup (Equiv.Perm X)) (hR : IsPGroup 2 R)
    (htrans : IsPretransitive R X)
    (g : Subgroup.normalizer (R : Set (Equiv.Perm X))) (hg : g ^ 5 = 1)
    (hfixed : Nat.card (Function.fixedPoints g.val) = 2)
    (K : Subgroup (Equiv.Perm X)) (hKR : K ≤ R)
    (hmin : ∀ k : K, k ≠ 1 → 27 ≤ k.val.support.card) : Nat.card K ≤ 32 := by
  rcases ThirtyTwoTwoGroupCenter.card_cases hX R hR htrans g hg hfixed with hZ | hZ | hZ
  · exact ThirtyTwoTwoGroupSmallCenter.card_le_thirty_two hX R hR htrans g hg hfixed hZ K hKR hmin
  · exact ThirtyTwoTwoGroupLargeCenter.card_le_thirty_two hX R htrans (by omega) K hKR hmin
  · exact ThirtyTwoTwoGroupLargeCenter.card_le_thirty_two hX R htrans (by omega) K hKR hmin

end FiveTransitive.ThirtyTwoTwoGroupBound

end CFSG
