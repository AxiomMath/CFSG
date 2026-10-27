module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrth
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndMain
public import CFSG.LocalAnalysis.StandardType.GGLayerCycMRestTwo
public import CFSG.LocalAnalysis.StandardType.GGRemStdSubResidualsU
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallLinTwo
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvd63

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType

theorem ggRemainderStdSubTableB_of_residualsULCOU
    (hTE6 : GGTableBTwE6Round12Lang)
    (hR5 : GGStdSubIOneProperInputOn GGIOneProperRestFiveLabel)
    (hsR : GGStdSubSmallInputOn fun p lab =>
      ((GGStdSubSmallRest5Label p lab ∧ ¬ GGLinTwoLabel p lab) ∧
        ¬ GGStdSubSmallOrthLabel p lab) ∧ ¬ (GGUnitDvd63Label p lab ∧ 2 ≤ lab.n))
    (hLie : GGLieLayerInput) (h1 : SmallOrth.PlusSplitInput) (h2 : SmallOrth.PlusTwoInput)
    (h3 : SmallOrth.MinusSplitInput) (h4 : SmallOrth.MinusUnitInput)
    (h5 : SmallOrth.TwDFourInput) :
    GGRemainderStdSubTableB :=
  ggRemainderStdSubTableB_of_residualsU hTE6
    (ggStdSubIOneProperInputOn_restNarrow_of_restFive ggLNoncyclicInput_holds
      ggIOneMoreFieldCorFourTwoInput_holds ggIOneMoreOrthEndNodeInput_holds hR5)
    (ggStdSubSmallInputOn_of_not_linTwo (ggStdSubSmallInputOn_of_not_orth h1 h2 h3 h4 h5
      ((ggStdSubSmallInputOn_unitDvd63_two_le.or hsR).mono fun p lab hT => by
        by_cases hl : GGUnitDvd63Label p lab ∧ 2 ≤ lab.n
        · exact Or.inl hl
        · exact Or.inr ⟨hT, hl⟩)))
    (ggLayerCenterCyclicModelRestTwo_of_kfacts hLie)

end CFSG.Yardstones.M3f9567aba59d
