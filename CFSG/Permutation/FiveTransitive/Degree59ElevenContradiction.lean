module

public import CFSG.Permutation.FiveTransitive.Degree59ElevenContradictionCore
public import CFSG.Permutation.FiveTransitive.Degree59ThreeFree
public import CFSG.Permutation.FiveTransitive.Degree59LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree59ElevenContradiction

open MulAction

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 59)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) : False := by
  exact Degree59ElevenContradictionCore.excluded_of_three_eleven_free P hcard h5
    (Degree59ThreeFree.not_dvd_five_fixer P hcard h5 hnotAlt)
    (fun s hs => Degree59LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs
      11 (by decide) (by omega))

end FiveTransitive.Degree59ElevenContradiction

end CFSG
