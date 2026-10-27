module

public import CFSG.Quasithin.H13.GoldschmidtC137H6ToC
public import CFSG.Quasithin.H13.GoldschmidtC137CDict

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace H6Frame

variable [Finite G] {X T V L P : Subgroup G} {h : H6Ctx X T V L P} (F : H6Frame h)

theorem card_ρ (K : Subgroup (Gp 6)) : Nat.card (K.map F.ρ) = Nat.card K :=
  F.toC137.card_ρ K

theorem card_fixV_ρ (K : Subgroup (Gp 6)) :
    Nat.card (fixV (K.map F.ρ)) = cK F.k * Nat.card (fixV (K.map (Mod.act 6 Mod.ut0))) :=
  F.toC137.card_fixV_ρ K

end H6Frame

end CFSG.Quasithin.H13.U3.GC137
