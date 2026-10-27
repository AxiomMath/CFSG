module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R6_39 (D : Data G) : Prop :=
  ∀ V : Subgroup G, InCalVStar D.M V → ¬ CFSG.CGT.Timmesfeld75.IsTI V

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
