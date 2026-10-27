module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOdd
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BEven
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BSporAll
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddFamilies

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem asc80ThmB_of_seitzFour
    (hS : SeitzFour fun X _ => CFSG.Models.OddLieType X ∧
      ¬ CFSG.Models.LieModel X .PSL 2 5 1 ∧ ¬ CFSG.Models.LieModel X .PSL 2 3 2) : Asc80ThmB :=
  asc80ThmB_of_cases asc80ThmBCase_alt (asc80ThmBCase_oddLieType_of_seitzFour hS)
    asc80ThmBCase_evenLieType asc80ThmBCase_sporadic

theorem asc80ThmB_holds :
    Asc80ThmB :=
  asc80ThmB_of_seitzFour seitzFour_oddLieType_of_families

end CFSG.LocalAnalysis.WeakClosure81

end
