module

public import CFSG.Quasithin.H13.A5S136r
public import CFSG.Quasithin.H13.A5Close1321c
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.Vol2.Ch1EightFourMain
public import CFSG.Quasithin.Background.SmithB42G2IdFact
public import CFSG.Quasithin.Background.SmithB42Holds
public import CFSG.Quasithin.Background.B5NonSQTK

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem fin136_of_hubs
    (h1323 : Input1323Two) (h1336 : Input1336) (h523 : Stmt5_2_3) (h312 : A312ForSQTK)
    (hD310 : D310) (hD391 : D391) (h45 : AsB45) : Fin136 :=
  fin136_of_ident h1323 h1336 h523 Vol2Native.a37ForSQTKCat_proved a38ForSQTKCat_holds
    Vol2Native.a39ForSQTKCat_proved h312 (Ch1Four.lemma128Four_of h312) hD310 hD391
    (insp4_of_inputs asA21SQTKSection factG2Cayley_holds asB42_holds h45 hD310)
    (endL34K_of h1323 h1336 asA21SQTKSection factG2Cayley_holds asB42_holds h45 hD310)

end CFSG.Quasithin.H13.A5
