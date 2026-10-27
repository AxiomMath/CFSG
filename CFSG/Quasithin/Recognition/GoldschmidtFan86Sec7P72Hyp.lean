module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Cnt3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem P72.lab3_of_fan512 {F : FanTree Γ G} {L : ZLab Γ G} (h : Fan512 F L) : P72.Lab3 F L :=
  h.2.2.1

theorem fan_7_2_of_fan512 {F : FanTree Γ G} {L : ZLab Γ G} (h : Fan71c F L) (h512 : Fan512 F L)
    (h40 : Fan40 F) (h64 : Fan64 F) : Fan72a F L ∧ Fan72b F L :=
  fan_7_2 h (P72.lab3_of_fan512 h512) h40 h64

end CFSG.Quasithin.Fan86
