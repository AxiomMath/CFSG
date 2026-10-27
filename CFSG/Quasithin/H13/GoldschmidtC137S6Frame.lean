module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Ctx

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S6Ctx

variable [Finite G] {X T V L P M : Subgroup G} (h : S6Ctx X T V L P M)
include h

theorem kmodel : ∃ k, (k = B3.Mod.ut0 ∨ k = B3.Mod.u0) ∧ Nonempty (KModel k (autI h.hVe L)) :=
  h.hmod

end S6Ctx

end CFSG.Quasithin.H13.U3.GC137
