module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91GammaCore
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91GammaA7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91GammaM22
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91GammaL3U3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)

theorem r891GammaList_holds :
    ∀ (Y : Type) [Group Y] [Finite Y], R891List896 Y → ∀ R : Subgroup Y,
      IsExtraspecialExpP 3 1 ↥R → center Y ≤ R →
      rankThreeGamma 1 3 (R.map (QuotientGroup.mk' (center Y))) ≠ ⊤ → R891List897 Y :=
  r891GammaList_of r891GammaA7_holds r891GammaM22_holds r891GammaL3_holds r891GammaU3_holds

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
