module

public import CFSG.Permutation.FiveTransitive.Degree69FactorizationContradiction
public import CFSG.Permutation.FiveTransitive.Degree69TwoExponent
public import CFSG.Permutation.FiveTransitive.Degree69ThreeBound

public section

namespace CFSG

namespace FiveTransitive.Degree69Classification
open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  exact Degree69FactorizationContradiction.excluded_of_power_bounds P hcard h5 hnotAlt s hs
    (Degree69TwoExponent.two_exponent_le_six P hcard h5 hnotAlt s hs)
    (Degree69ThreeBound.pow_dvd_five_fixer_le_ten P hcard h5 hnotAlt s hs)

end FiveTransitive.Degree69Classification

end CFSG
