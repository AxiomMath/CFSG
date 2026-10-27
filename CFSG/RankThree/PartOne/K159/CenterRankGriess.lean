module

public import CFSG.RankThree.PartOne.K159.CenterRankClosed
public import CFSG.RankThree.PartOne.KP.BExclusion
public import CFSG.RankThree.PartOne.KP.Fi22Section
public import CFSG.RankThree.PartOne.KP.MSectionMonster
public import CFSG.RankThree.PartOne.KS.FischerSections
public import CFSG.RankThree.PartOne.MultRes.Trim

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.MultRes

theorem centerRankFour_of_griess_of_M_section
    (hbridge : TauCetiCatalogBridge)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hMB : SimplePresentationMHasBSection) : CenterRankFour :=
  have h2224 := sectionsForceEvenRankFour_fi23_fi24prime sectionsForceEvenRankFour_Fi22
    hasSection_fi23_fi22 hasSection_fi24prime_fi23
  centerRankFour_of_residual_trim hbridge hGA sporadicResidualKernelsTrim_holds
    sectionsForceEvenRankFour_Fi22 h2224.1 h2224.2 sectionsForceEvenRankFour_B
    (simplePresentationM_sections_of_B_section sectionsForceEvenRankFour_B hMB)

theorem centerRankFour_of_griess
    (hbridge : TauCetiCatalogBridge)
    (hGA : CFSG.Open.GriessAllModelsStatement) : CenterRankFour :=
  centerRankFour_of_griess_of_M_section hbridge hGA simplePresentationMHasBSection_holds

end CFSG.RankThree.PartOne.K159
