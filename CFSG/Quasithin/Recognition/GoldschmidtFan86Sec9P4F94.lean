module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94A
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94T2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_9_4a {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h65 : Fan65 F)
    (h81 : Fan81 F L) (h82 : Fan82 F L) (h83b : Fan83b F L) (h512 : Fan512 F L) :
    Fan94a F L := fun S =>
  S.fan94a_of F h7 h65 h81 h82 h83b h512 (S.top_lower F h7 h81 h512)

theorem fan_9_4b {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h65 : Fan65 F)
    (h81 : Fan81 F L) (h82 : Fan82 F L) (h83b : Fan83b F L) (h512 : Fan512 F L) :
    Fan94b F L := fun S =>
  S.fan94b_of F h7 h65 h81 h82 h83b h512 (S.w_mem_nbrStab_beta F h7.2.2.1)
    (S.wA_mem_nbrStab_beta F h7.2.2.1 1) (S.c_mem_nbrStab_beta F h7.1 h7.2.2.1)
    (S.top_lower F h7 h81 h512)

end CFSG.Quasithin.Fan86
