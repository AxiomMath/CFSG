module

public import CFSG.Quasithin.H13.GoldschmidtCTK
public import CFSG.Quasithin.H13.GoldschmidtCTKHolds
public import CFSG.Quasithin.H13.A6S1514G248
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal

public section


namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.CTK

theorem input13515CTK_of_lemmas
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) :
    Input13515CTK :=
  input13515CTK_of h13315 h1356two (obl13_5_14Six_of_1356 h13315 h1356two)
    Vol2Native.a37ForSQTKCat_proved
    (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)
    Vol2Native.a39ForSQTKCat_proved Vol2Native.a36CoreForSQTKCat_proved l2MultiplierFact
    (fun X _ _ hX H N _ _ hna => CFSG.Milestones.cl_lit_sqtk_simple_list_section X hX H N hna)
    exclA5Block_holds

end CFSG.Quasithin.H13.A6
