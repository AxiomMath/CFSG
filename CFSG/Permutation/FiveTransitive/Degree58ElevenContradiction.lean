module

public import CFSG.Permutation.FiveTransitive.Degree58ElevenContradictionCore
public import CFSG.Permutation.FiveTransitive.Degree58ThreeFree
public import CFSG.Permutation.FiveTransitive.Degree58LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree58ElevenContradiction

open MulAction

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 58)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) : False := by
  exact Degree58ElevenContradictionCore.excluded_of_three_eleven_free P hcard h5
    (Degree58ThreeFree.not_dvd_five_fixer P hcard h5 hnotAlt)
    (fun s hs => Degree58LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs
      11 (by decide) (by omega))

end FiveTransitive.Degree58ElevenContradiction

end CFSG
