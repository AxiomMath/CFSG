module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Main
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2UMaxOrbit
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxAlt
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxSpor
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporTh
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxOddRow
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoMain
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Alt
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallChevOdd
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporON
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporAll
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmegaHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunCommute

public section

namespace CFSG.LocalAnalysis.WeakClosure81


theorem asch5_4_of_open (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) (h22 : Asch2_2Simple) :
    Asch5_4 :=
  have hFC := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_FunCommute_of_funHypOmega
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_FunHypOmega_holds
  have hFC3 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_FunCommuteThree_of_funHypOmega
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_FunHypOmega_holds
  asch5_4_of_inputs (asch54Chev2 hS) (asch54Alt_of hS) asch54Spor_holds
    (asch54ChevOdd_of_funCommute hS hFC hFC3)
    (asch80ThmA54_of_cases (asch80ThmA54Case_chev2 hS) (asch80ThmA54Case_alt hS)
        (asch80ThmA54Case_spor_of_gen asch54SporGenAt_of_ne_th asch54SporThGen_holds)
        (asch80ThmA54Case_oddLie hS k_Asch511SylowOvergroupsPSp4_holds hFC hFC3))
    asch54ONGen_holds h22

end CFSG.LocalAnalysis.WeakClosure81

end
