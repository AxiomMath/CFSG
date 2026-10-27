module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2FCase
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_8_5 (F : FanTree Γ G) (L : ZLab Γ G) (h7 : Fan7 F L) (h512 : Fan512 F L)
    (h517 : Fan517 F L) (h82a : Fan82a F L) (h83a : Fan83a F L) (h83b : Fan83b F L)
    (h83d : Fan83d F L) : Fan85 F L := by
  intro α D δ' hY
  obtain ⟨ν, hν, hνδ⟩ := exists_adj_adj_of_dist_two F.isTree
    (hY.2.2.2.2.1 : Γ.dist (D.alpha 0) δ' = 2)
  rcases Sec8P2F.nu_cases F h7 h83a h83b h83d hY hν hνδ with h | h
  · exact (Sec8P2F.case_nu F h7 h512 h517 h82a h83a h83b h83d hY hν hνδ h).elim
  · exact Sec8P2F.case_nu_inv F h7 h512 h83a h83b h83d hY hν hνδ h

end CFSG.Quasithin.Fan86
