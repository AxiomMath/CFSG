module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R922A5
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R922A5Stell
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R917A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R922A5Syl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem r922A5_of_r917A5
    (hKPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (D : Data G) (h912 : R912A5 D)
    (h917 : R917A5 D) : R922A5 D := by
  intro Y H D₃ S hY hA5 hR hSM hC
  have hIM : I9 H ≤ D.M := (I9_le_calCGS hKPSz hY hR
    (isSylowOf_pCoreOf_sup_I9 hY hA5 (h912 Y H D₃ S hY hA5 hR).1)).trans hC
  exact hY.1.2.1.2.1 ((h917 Y H D₃ S hY hA5 hR hSM).le.trans (sup_le inf_le_right hIM))

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
