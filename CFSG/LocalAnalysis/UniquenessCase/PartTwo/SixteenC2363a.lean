module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Unique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Hyp154

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_63a_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h22 : R1622 D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D) : R16_63a D := by
  intro V₀ V L hV hS hc
  have hs : s15 D.M V₀ V hV L = 2 := by
    rcases hc with hc | hc
    · exact hc.2.2.1
    · exact hc.2.2.1
  exact c23_hyp154_of_unique₁ D h22 hS.setting.hyp16 hS.setting.hyp151 hs
    (c23_unique₁ D hSg h61 h127 h1217 hS hc)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
