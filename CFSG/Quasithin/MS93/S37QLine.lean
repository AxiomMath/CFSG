module

public import CFSG.Quasithin.MS93.S37T1

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def QLineCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (C : Cfg M T L F), critDist (puAmalgam C.h.le) = 2 → IsOddRadical M T →
      C.T0bar = Q₁ F → C.k = 2

end CFSG.Quasithin.MS93.S37
