module

public import CFSG.Permutation.FiveTransitive.Degree36SylowTwoEntrance
public import CFSG.Permutation.FiveTransitive.Degree36TwoSubgroupExclusion

public section

namespace CFSG

namespace FiveTransitive.Degree36Classification

open MulAction SylowFixedActionCore

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  classical
  by_contra hnotAlt
  obtain ⟨s,_,hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset X)) (n := 5) (by simp [hcard])
  have hs' : (s : Set X).ncard = 5 := by simpa using hs
  let S : Sylow 2 (fixingSubgroup P (s : Set X)) := Sylow.nonempty.some
  obtain ⟨hQ,hlarge,hF,him⟩ := Degree36SylowTwoEntrance.fixed_six_and_image
    P hcard h5 hnotAlt (s : Set X) hs' S
  exact Degree36TwoSubgroupExclusion.excluded P hcard h5 hnotAlt
    (sylowImage X P (s : Set X) S) hQ hlarge hF him

end FiveTransitive.Degree36Classification

end CFSG
