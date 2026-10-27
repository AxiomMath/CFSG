module

import CFSG.GH74.EvenRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem gf2nTypeHyps_of_inCalVStar (D : Data G) {V : Subgroup G} (hV : InCalVStar D.M V) :
    CFSG.IsKProper G ∧ CFSG.IsCharacteristicPType G 2 ∧ CFSG.IsMaximalTwoLocal D.M ∧
      Maximal (fun W : Subgroup G => W ≤ D.M ∧ D.M ≤ normalizer (W : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 W) V := by
  have := D.standing.simple
  refine ⟨CFSG.ComponentClassification.CatalogueKProper.isKProper_of_kProper
    (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.mp D.standing.kProper),
    CFSG.GH74.isCharTwoType_iff.mp D.standing.charTwo,
    ⟨D.maxLocal.1, fun H hMH hH => hMH.ne (D.maxLocal.2 H hH hMH.le).symm⟩, ?_⟩
  exact ⟨hV.1.2, fun W hW hVW => (hV.2 W ⟨fun h => hV.1.1 (le_bot_iff.mp (h ▸ hVW)), hW⟩ hVW).le⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
