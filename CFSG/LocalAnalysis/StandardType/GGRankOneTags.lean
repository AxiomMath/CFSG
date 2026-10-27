module

public import CFSG.LocalAnalysis.StandardType.GGRankOneTagsA
public import CFSG.LocalAnalysis.StandardType.GGRankOneTagsE

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank

section Tag

theorem ggRankOneModel_of_tag {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) (hrank : 3 ≤ bnRank t n) :
    GGRankOneModel (ggU t n f).D (GaloisField 2 f) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact ggRankOneModel_PSL hadm hrank
  · exact ggRankOneModel_POmegaPlus hadm hrank
  · exact ggRankOneModel_E6 hadm hrank
  · exact ggRankOneModel_E7 hadm hrank
  · exact ggRankOneModel_E8 hadm hrank

end Tag

end CFSG.StandardType
