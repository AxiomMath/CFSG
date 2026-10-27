module

public import CFSG.Permutation.FiveTransitive.FourTransitiveEvenStabilizer
public import CFSG.Permutation.FiveTransitive.MinimalNormalFour

public section

namespace CFSG

namespace FiveTransitive.NormalFourEvenStabilizer

theorem exists_order_two_fixing_in_normal
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : 28 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (hnotAlt : ¬ alternatingGroup X ≤ P)
    (N : Subgroup P) [N.Normal] [Nontrivial N]
    (s : Set X) (hs : s.ncard = 4) :
    ∃ g : N, orderOf g = 2 ∧ ∀ x ∈ s, g • x = x := by
  exact FourTransitiveEvenStabilizer.exists_order_two_fixing N X (by omega)
    (MinimalNormalFour.four_of_normal_of_not_alternating X P (by omega) h5 hnotAlt N) s hs

end FiveTransitive.NormalFourEvenStabilizer

end CFSG
