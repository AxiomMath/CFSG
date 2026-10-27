module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9TailEdge
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94Fin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95abB
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95d6
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F96
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F97
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XFinal
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Pres5
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F98Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F99Main

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem p5Hyp_of (F : FanTree Γ G) (L : ZLab Γ G) (h7 : Fan7 F L) (h65 : Fan65 F)
    (h512 : Fan512 F L) (h517 : Fan517 F L) : P5Hyp F L := by
  have P := fan8_parts_of F L h7 h65 h512 h517
  have h92 : Fan92 F L := fan_9_2 h7 h65 h512 P.fan82 P.fan83 P.fan85 P.fan86
  have h93 : Fan93 F L := fan_9_3 F L h7 P.fan81 P.fan82 P.fan83 h512
  have h94 : Fan94 F L := fan_9_4 h7 h65 P.fan81 P.fan82 P.fan83b h512
  have h95 : Fan95 F L := fan_9_5 h7 P h512 (fan_9_5c F L h7 P.fan82 P.fan83 P.fan85 h512)
      (fan_9_5d F L h7 P.fan81 P.fan82 P.fan83 P.fan85 P.fan87 h512)
  have h96 : Fan96 F L := fan_9_6 h7 P.fan82.1 P.fan83b P.fan83c P.fan83d P.fan85 h512 h95
  have h97 : Fan97 F L :=
    fan_9_7 h7 P.fan82.1 P.fan83b P.fan83c P.fan83d P.fan85 h512 h93 h95 h96
  have h98 : Fan98 F L := fan_9_8 h7 P h65 h512 h92 h93 h95 h97
  have h99 : Fan99 F L := fan_9_9 h7 P h65 h512 h92 h95 h96 h98
  exact ⟨h7, P, h65, h512, h92, h93, h94, h95, h98, h99⟩

theorem fan915_of (F : FanTree Γ G) (L : ZLab Γ G) (h7 : Fan7 F L) (h65 : Fan65 F)
    (h512 : Fan512 F L) (h517 : Fan517 F L) : Fan915 F L :=
  fan_9_15 (p5Hyp_of F L h7 h65 h512 h517)

theorem fanTail_proved : FanTail :=
  fanTail_of_items
    (fun _ _ _ _ _ F L h7 h65 _ h517 h512 => (fan8_parts_of F L h7 h65 h512 h517).fan84a)
    (fun _ _ _ _ _ F L h7 h65 _ h517 h512 =>
      secCfgExists_proved F L h7 h65 (fan8_parts_of F L h7 h65 h512 h517).fan81
        (fan8_parts_of F L h7 h65 h512 h517).fan83a (fan8_parts_of F L h7 h65 h512 h517).fan83b
        (fan8_parts_of F L h7 h65 h512 h517).fan84a (fan8_parts_of F L h7 h65 h512 h517).fan87)
    (fun _ _ _ _ _ F L h7 h65 _ h517 h512 => fan915_of F L h7 h65 h512 h517)

end CFSG.Quasithin.Fan86
