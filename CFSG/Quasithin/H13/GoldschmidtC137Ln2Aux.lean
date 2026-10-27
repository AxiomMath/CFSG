module

public import CFSG.Quasithin.H13.GoldschmidtC137Pt1Aux

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

theorem rk_map_act (K : Subgroup (Gp 6)) : rk (K.map (Mod.act 6 Mod.ut0)) = rk K := by
  unfold rk
  rw [card_map_act]

theorem rAV_of_rank {K : Subgroup (Gp 6)}
    (hk : rk K = 1 ∧ rkIdx (fixV (K.map (Mod.act 6 Mod.ut0))) = 1) :
    rAV (K.map (Mod.act 6 Mod.ut0)) = 1 := by
  unfold rAV
  rw [hk.2, rk_map_act, hk.1]
  norm_num

end CFSG.Quasithin.H13.U3.GC137
