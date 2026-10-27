module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95Two
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95A4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95S3
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem r95Two_of_inputs (hK32 : UCK.K32) (hK461 : UCK.K461)
    (hK462 : UCK.K462) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (D : Data G) :
    R95Two D := by
  have h92 : R92 D := r92_of_inputs hK32 hSch D
  intro Y H D₃ hyp hH hX
  refine ⟨r95_sylow_clause hK461 hSch hyp hH h92 hX, ?_⟩
  by_cases hLM : img9 H (L9 Y H) ≤ img9 H (H ⊓ D.M)
  · exact Or.inl (r95_caseA hK461 hK462 hSch hyp hH h92 hX hLM)
  · exact Or.inr ((r95_caseB hyp hH h92 hX hLM).imp fun e he => ⟨he.1, he.2.1, he.2.2.1⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
