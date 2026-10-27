module

public import CFSG.Quasithin.Background.C24PfC
public import CFSG.Quasithin.Background.C2PushMain
public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem asc24One_holds :
    ∀ (G : Type) [Group G] [Finite G], ASC24One G := fun G _ _ =>
  C24Pf.asc24One_of (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved)
    (a38ForSQTK_of_cat (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved))
    (fun _ _ h => Vol2Native.L122A.isSimpleGroup_of_a38Types h) (VolI.asc129Statement_holds G)

theorem asc24OneMoved_holds :
    ∀ (G : Type) [Group G] [Finite G], ASC24OneMoved G := fun G _ _ =>
  asc24OneMoved_of_asc24One (asc24One_holds G)

end CFSG.Quasithin.H13.U3
