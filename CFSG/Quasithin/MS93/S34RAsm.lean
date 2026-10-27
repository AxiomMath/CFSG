module

public import CFSG.Quasithin.MS93.SkItems

public section

namespace CFSG.Quasithin.MS93.S34R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def S34RDesc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    2 < critDist (puAmalgam h.le) →
    (IsSL3U M T L ∧ ¬ IsSL3Full M T L) ∨ (IsSp4U M T L ∧ ¬ IsSp4Full M T L) →
    ∃ T' : Subgroup G, T' ≤ T ∧ T' ≠ T ∧ PUHyp (L ⊔ T') T' L

variable {G : Type} [Group G]

variable [Finite G] {M T L : Subgroup G}

end CFSG.Quasithin.MS93.S34R
