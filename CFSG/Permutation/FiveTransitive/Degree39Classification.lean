module

public import CFSG.Permutation.FiveTransitive.Degree39ThirteenNormalizer
public import CFSG.Permutation.FiveTransitive.Degree39ThirteenTransfer

public section

namespace CFSG

namespace FiveTransitive.Degree39Classification
open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  classical
  by_contra hnotAlt
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let S : Sylow 13 P := Sylow.nonempty.some
  obtain ⟨hS,hN⟩ := Degree39ThirteenNormalizer.card_eq_thirteen P hcard h5 hnotAlt S
  exact Degree39ThirteenTransfer.excluded_of_normalizer_card P hcard h5 S hS hN

end FiveTransitive.Degree39Classification

end CFSG
