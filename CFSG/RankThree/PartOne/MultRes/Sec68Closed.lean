module

public import CFSG.RankThree.PartOne.MultRes.Trim
public import CFSG.RankThree.PartOne.KP.Fi22Section
public import CFSG.RankThree.PartOne.KS.FischerSections
public import CFSG.RankThree.PartOne.KP.BExclusion
public import CFSG.RankThree.PartOne.KP.MSectionMonster

public section

namespace CFSG.RankThree.PartOne.MultRes

open CFSG CFSG.RankThree.PartOne

theorem sec6Eight_of_griess_of_M_section
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hMB : SimplePresentationMHasBSection) : Sec6EightMultipliers :=
  have h2224 := sectionsForceEvenRankFour_fi23_fi24prime sectionsForceEvenRankFour_Fi22
    hasSection_fi23_fi22 hasSection_fi24prime_fi23
  Mult.sec6Eight_of_residual_trim hGA sporadicResidualKernelsTrim_holds
    sectionsForceEvenRankFour_Fi22 h2224.1 h2224.2 sectionsForceEvenRankFour_B
    (simplePresentationM_sections_of_B_section sectionsForceEvenRankFour_B hMB)

theorem sec6Eight_of_griess
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Sec6EightMultipliers :=
  sec6Eight_of_griess_of_M_section hGA simplePresentationMHasBSection_holds

end CFSG.RankThree.PartOne.MultRes
