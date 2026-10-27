module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SylowNormalizer859

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

theorem r859_of_r858 {G : Type} [Group G] [Finite G] {D : Data G} (h858 : R858 D) : R859 D := by
  intro L Q P hcex
  rcases h858 L Q P hcex with hM | ⟨hcard, -⟩
  · exact hcex.sylowP.le.trans hM
  · exact sylow_le_normalizer_of_ncard_conjSetOf_le_two hcex.sylowP hcex.mem hcard.le

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
