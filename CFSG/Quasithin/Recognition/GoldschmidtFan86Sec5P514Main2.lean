module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Z5
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4NineMain

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_5_14_of_sec4 (F : FanTree Γ G) (h28 : Fan28) (h211 : Tutte.TutteTree) (h33 : Fan33 F)
    (h51a : Fan51a F) (h53b : Fan53b F) (h53c : Fan53c F) (h54 : Fan54 F) (h55a : Fan55a F)
    (h55b : Fan55b F) (h55c : Fan55c F) (h510 : Fan510 F) (h511 : Fan511 F)
    (h512cen : Fan512cen F) (h512b : Fan512b F) (h512c : Fan512c F) (h513a : Fan513a F) :
    Fan514 F :=
  fan_5_14 F
    (fun h40 T₀ h => by
      obtain ⟨T', -, hT'⟩ := fan48_1 F h40 h28 T₀ h
      exact ⟨T', hT'⟩)
    (fun h40 T hPi a b c hθ hc => fan47 T F h40 hPi hθ hc)
    (fun h40 T hI a b hθ => (fan48_concl F h40 h28 h211 T hI hθ).length)
    (fun h40 T hI => fan49_main_five F h40 h33 (fan48_two F h40 h28 h211) hI)
    h51a h53b h53c h54 h55a h55b h55c h510 h511 h512cen h512b h512c h513a

end CFSG.Quasithin.Fan86
