module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2Asm
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2FMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2KFin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3ExY

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure Fan8Parts (F : FanTree Γ G) (L : ZLab Γ G) : Prop where
  fan81 : Fan81 F L
  fan82 : Fan82 F L
  fan83a : Fan83a F L
  fan83b : Fan83b F L
  fan83c : Fan83c F L
  fan83d : Fan83d F L
  fan83e : Fan83e F L
  fan84a : Fan84a F L
  fan85 : Fan85 F L
  fan86 : Fan86abc F L
  fan87 : Fan87 F L

namespace Fan8Parts

variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem fan83 (P : Fan8Parts F L) : Fan83 F L :=
  ⟨P.fan83a, P.fan83b, P.fan83c, P.fan83d, P.fan83e⟩

end Fan8Parts

theorem fan8_parts_of (F : FanTree Γ G) (L : ZLab Γ G) (h7 : Fan7 F L) (h65 : Fan65 F)
    (h512 : Fan512 F L) (h517 : Fan517 F L) : Fan8Parts F L := by
  have h81 : Fan81 F L := fan_8_1 h7
  have h82 : Fan82 F L := fan_8_2 h7 h81 h512
  have h83 : Fan83 F L := fan_8_3 h7 h81 h82.1 h512
  have h84a : Fan84a F L := fan_8_4a F L h7 h83.2.2.1
  exact ⟨h81, h82, h83.1, h83.2.1, h83.2.2.1, h83.2.2.2.1, h83.2.2.2.2, h84a,
    fan_8_5 F L h7 h512 h517 h82.1 h83.1 h83.2.1 h83.2.2.2.1,
    fan_8_6_of F L h7.1 h7.2.2.1 h7.2.2.2.2.2.2.2.2 h65 h83.1 h83.2.2.1 h83.2.2.2.1 h84a
      (fan_D10_exists h7),
    fan_8_7 h7 h512 h82.1 h83 h84a⟩

end CFSG.Quasithin.Fan86
