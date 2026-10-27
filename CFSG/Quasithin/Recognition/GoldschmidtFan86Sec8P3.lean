module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3A
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3C

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_8_6_of (F : FanTree Γ G) (L : ZLab Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L)
    (h75 : Fan75 F L) (h65 : Fan65 F) (h83a : Fan83a F L) (h83c : Fan83c F L)
    (h83d : Fan83d F L) (h84a : Fan84a F L) (hD : D10YPairExists F L) : Fan86abc F L :=
  ⟨fan_8_6a F L h71c h75 h83a h83c h83d h84a hD, fan_8_6b F L h71a h71c h75 h65 h84a,
    fan_8_6c F L h71c⟩

end CFSG.Quasithin.Fan86
