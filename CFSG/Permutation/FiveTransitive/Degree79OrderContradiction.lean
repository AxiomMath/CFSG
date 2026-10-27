module

public import CFSG.Permutation.FiveTransitive.Degree79PureTwo
public import CFSG.Permutation.FiveTransitive.Degree79SeventyNineNormalizer
public import CFSG.Permutation.FiveTransitive.Degree79SeventyNineNumeric

public section

namespace CFSG

namespace FiveTransitive.Degree79OrderContradiction
open MulAction

private theorem excluded_of_five_set
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hbound : ∀ S : Sylow 2 (fixingSubgroup P s), Nat.card S ≤ 2 ^ 22) : False := by
  obtain ⟨a,ha,_,hP⟩ := Degree79PureTwo.card_exponent P hcard h5 hnotAlt s hs hbound
  obtain ⟨d,k,hd,hk,he⟩ := Degree79SeventyNineNormalizer.constraints P hcard h5 hnotAlt
  rw [hP] at he
  exact Degree79SeventyNineNumeric.excluded ha
    (Degree79SeventyNineNumeric.residue hd hk he)

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hbound : ∀ (s : Set X), s.ncard = 5 →
      ∀ S : Sylow 2 (fixingSubgroup P s), Nat.card S ≤ 2 ^ 22) : False := by
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  exact excluded_of_five_set P hcard h5 hnotAlt s hs (hbound s hs)

end FiveTransitive.Degree79OrderContradiction

end CFSG
