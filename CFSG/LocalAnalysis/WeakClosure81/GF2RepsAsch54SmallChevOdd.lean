module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54ChevOdd
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Ree
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54OddGen
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallMain
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallSp4

public section

namespace CFSG.LocalAnalysis.WeakClosure81


theorem asch54ChevOdd_of_funCommute (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hFC : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_FunCommute)
    (hFC3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_FunCommuteThree) :
    Asch54ChevOdd := by
  refine asch54ChevOdd_of hS asch54Case_ree ?_
  intro Q _ _ L T hKQ hLn hLs hLnab hC ⟨hodd, hsec, hree⟩ hL0 hT hnu
  by_cases hsm : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ Asch511SmallLie ↥L r
  · exact asch54Case_oddLie_small_of_psp4 hS k_Asch511SylowOvergroupsPSp4_holds Q L T hKQ hLn
      hLs hLnab hC hsm hL0 hT hnu
  · exact asch54Case_oddLie_generic hFC hFC3 Q L T hKQ hLn hLs hLnab hC
      ⟨hodd, hsec, hree, hsm⟩ hL0 hT hnu

end CFSG.LocalAnalysis.WeakClosure81

end
