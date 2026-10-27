module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Std
public import CFSG.Quasithin.H13.GoldschmidtC137CFrame

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace S6Frame

variable [Finite G] {X T V L P M : Subgroup G} {h : S6Ctx X T V L P M}

abbrev toC137 (F : S6Frame h) : C137Frame h.hVe X T L :=
  ⟨F.k, F.hk, F.Φ, F.ρ, F.inj, F.equiv, F.hA, F.hX, F.hT⟩

end S6Frame

end CFSG.Quasithin.H13.U3.GC137
