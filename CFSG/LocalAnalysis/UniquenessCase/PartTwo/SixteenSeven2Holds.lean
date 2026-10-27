module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Twelve
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Eighteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Nineteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Twenty
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677Glue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_7F_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h1217 : R1217 D) (h8 : R16_8F D) (h10 : R16_10_1 D) (h11 : R16_11 D) (h13 : R16_13_1 D)
    (h13b : R16_13_2 D) (h14 : R16_14 D) (h15 : R16_15 D) (h16 : R16_16 D) : R16_7F D := by
  have h12 : R16_12 D := sixteen_seven2_twelve D h10 h11
  have h17 : R16_17 D := sixteen_seven2_seventeen D h1217 h12 h15
  have h18 : R16_18 D := r16_18_holds D hSg h1219 h12 h14 h15
  have h19 : R16_19 D := r16_19_holds D hSg h1219 h12 h13 h14 h15 h17
  have h20 : R16_20 D := r16_20_holds D hSg h1219 h12 h13 h13b h14 h16 h18 h19
  exact sixteen_seven2_of_steps_F D h8 h12 h13 h17 h20

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
