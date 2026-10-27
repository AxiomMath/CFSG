module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2e
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2cMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2d1Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2a

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_8_3 {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h82 : Fan82a F L) (h512 : Fan512 F L) : Fan83 F L :=
  ⟨fan_8_3a h7 h81 h82 h512, fan_8_3b h7 h81 h512, fan_8_3c h7 h81 h512,
    ⟨fan_8_3d1 h7 h81 h512, fan_8_3d2 h7 h81 h82 h512⟩, fan_8_3e h7 h81 h82 h512⟩

end CFSG.Quasithin.Fan86
