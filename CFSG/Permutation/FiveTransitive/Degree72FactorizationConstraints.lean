module

public import CFSG.Permutation.FiveTransitive.Degree72PureTwo
public import CFSG.Permutation.FiveTransitive.Degree72FactorizationNumeric
public import CFSG.Permutation.FiveTransitive.Degree72SeventyOneNormalizer
public import CFSG.Permutation.FiveTransitive.Degree72TwentyThreeRefined

public section

namespace CFSG

namespace FiveTransitive.Degree72FactorizationConstraints
open MulAction

private theorem excluded_of_five_set
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : False := by
  obtain ⟨a,_,ha,_,hP⟩ := Degree72PureTwo.card_exponent P hcard h5 hnotAlt s hs
  obtain ⟨d,k,hd,hk,he⟩ := Degree72SeventyOneNormalizer.constraints P hcard h5 hnotAlt
  obtain ⟨c,j,hc,hj,hf⟩ := Degree72TwentyThreeRefined.constraints P hcard h5 hnotAlt
  rw [hP] at he hf
  exact Degree72FactorizationNumeric.excluded ha
    (Degree72FactorizationNumeric.residue71 hd hk he)
    (Degree72FactorizationNumeric.residue23 hc hj hf)

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) : False := by
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  exact excluded_of_five_set P hcard h5 hnotAlt s hs

end FiveTransitive.Degree72FactorizationConstraints

end CFSG
