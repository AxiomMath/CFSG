module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5FramePos
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5FrameE78
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5FrameE6
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5FrameF4

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section Frame

theorem ggG5_frame_exists
    {t : StatedLieTag} {p f : ℕ} (ht : GGExcFive t) (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f) :
    Nonempty (GGLangFrame t p f ht) := by
  rcases eps_cases p f with hε | hε
  · exact ggG5_frame_pos ht hp hp2 hε
  · rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ggG5_frame_neg_F4 _ hf hε
    · exact ggG5_frame_neg_E6 _ hf hε
    · exact ggG5_frame_neg_E7 _ hf hε
    · exact ggG5_frame_neg_E8 _ hf hε
    · exact ggG5_frame_neg_twistedE6 _ hf hreg hε

end Frame

end CFSG.StandardType.GGFinModel.G5
