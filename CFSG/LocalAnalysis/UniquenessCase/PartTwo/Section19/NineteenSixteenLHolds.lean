module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSixteenL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSixteenL4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSixteenL5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSixteenL8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {G : Type} [Group G] [Finite G]

section Certified


theorem gap19_16_L_holds (D : Data G) (h85 : CFSG.AGLEmbedding.Asc81bEightFive)
    (hC : K_19_16_census) : Gap19_16_L D := by
  intro V₀ V p L A t B r Y N Dsub H S h h15 h11 hc
  rcases hc with ⟨h3, hL3⟩ | ⟨h4, -⟩ | ⟨h5, -⟩ | ⟨h8, -⟩
  · exact p19_16_of_nineThreeThree h h11 h15 h3 hL3
  · exact p19_16_of_nineThreeFour h85 hC h h11 h15 h4
  · exact p19_16_of_nineThreeFive h85 h h11 h15 h5
  · exact p19_16_of_nineThreeEight h h11 h8

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
