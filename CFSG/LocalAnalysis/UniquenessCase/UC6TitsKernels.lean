module

public import CFSG.LocalAnalysis.UniquenessCase.UC6TitsAut
public import CFSG.LocalAnalysis.UniquenessCase.UC6AutEbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Blueprint (LieModel)

namespace Mz614

section KC


variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem kc633_of_tits (h620 : m.C620) (hr : m.r = 5) (hT : LieModel m.Lbar .Tits 0 2 1) : m.KC633 :=
  m.kc633_of_abs (TitsAut.absKC hT hr m.Ebar (by rw [m.card_Ebar h620, hr]))

theorem kinv633_of_tits (h620 : m.C620) (hr : m.r = 5) (hT : LieModel m.Lbar .Tits 0 2 1) : m.KInv633 :=
  m.kinv633_of_abs (TitsAut.absKInv hT m.Ebar (by rw [m.card_Ebar h620, hr]))

end KC

section KN


variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem kn633_of_tits (h620 : m.C620) (hr : m.r = 5) (hT : LieModel m.Lbar .Tits 0 2 1) : m.KN633 :=
  m.kn633_of_abs (TitsAut.absKN hT hr _ m.Ebar (by rw [m.card_Ebar h620, hr]))

end KN

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
