module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24C4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_24c_holds (D : Data G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D) (h26 : R16_26 D) : R16_24c D := by
  have h22 : R1622 D := R1622_of_R1621 D hSg h1219 h21
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  refine r16_24c_of_lt D h126 fun V₀ V L hV hS hc => ⟨?_, ?_⟩
  · exact Sixteen24.k_lt_rParam_of_hyp125 D hSg h1219 hx h61 hS.setting.hyp16.hyp125
  · rcases hc with h3 | h4 | h7 | h8
    · exact Sixteen24.k_lt_betaN_of_case3 D hSg h1219 h22 h61 h127 h1217 hS h3
    · exact Sixteen24.k_lt_betaN_of_case4 D hSg h1219 h1217 hS h4
    · exact Sixteen24.k_lt_betaN_of_case7 D hS h7
    · exact Sixteen24.k_lt_betaN_of_case8 D hSg h1219 h26 hS h8

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
