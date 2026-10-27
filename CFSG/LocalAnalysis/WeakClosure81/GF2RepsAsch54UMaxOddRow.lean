module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFun
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunThree

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54OddGen
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxG2Holds

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

theorem asch80ThmA54Case_oddLie (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hSp : K_Asch511SylowOvergroupsPSp4)
    (hFC : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_FunCommute)
    (hFC3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_FunCommuteThree) :
    Asch80ThmA54Case fun X _ => CFSG.Models.OddLieType X :=
  asch80ThmA54Case_oddLie_of hS hSp asch80G2Prime_holds
    fun _ _ _ _ _ _ _ hLn hLs hnab _ hP _ hT _ _ =>
      Or.inl (oddLie_generic_pRank_of_not_sl2Image hFC hFC3 (hLn := hLn) hLs hnab hP.1 hP.2.1
        hP.2.2.1 hP.2.2.2 hT)

end CFSG.LocalAnalysis.WeakClosure81

end
