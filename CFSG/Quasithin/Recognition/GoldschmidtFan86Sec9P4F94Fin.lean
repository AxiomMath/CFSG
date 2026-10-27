module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94I
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94I2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94T3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_9_4c {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h65 : Fan65 F)
    (h81 : Fan81 F L) (h82 : Fan82 F L) (h83b : Fan83b F L) (h512 : Fan512 F L) :
    Fan94c F L := fun S => by
  have h71c : Fan71c F L := h7.2.2.1
  have hw := S.w_mem_nbrStab_beta F h71c
  have hwA := S.wA_mem_nbrStab_beta F h71c 1
  have hc := S.c_mem_nbrStab_beta F h7.1 h71c
  have htop := S.top_lower F h7 h81 h512
  have hidx := (S.fan94_exact_of F h7 h65 h81 h82 h83b h512 hw hwA hc htop).1
  exact ⟨fun hC => S.exists_top_iso_two F h7 h81 h512 hidx hC,
    fun hC => S.exists_top_iso_four F h7 h81 h512 hidx hC,
    S.exists_mid_iso F h7 h65 h81 h82 h83b h512 hw hwA hc htop,
    S.exists_bottom_iso F h7 h65 h81 h82 h83b h512 hw hwA hc htop⟩

theorem fan_9_4 {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h65 : Fan65 F)
    (h81 : Fan81 F L) (h82 : Fan82 F L) (h83b : Fan83b F L) (h512 : Fan512 F L) :
    Fan94 F L :=
  ⟨fan_9_4a h7 h65 h81 h82 h83b h512, fan_9_4b h7 h65 h81 h82 h83b h512,
    fan_9_4c h7 h65 h81 h82 h83b h512⟩

end CFSG.Quasithin.Fan86
