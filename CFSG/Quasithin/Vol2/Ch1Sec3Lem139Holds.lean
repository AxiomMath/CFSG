module

public import CFSG.Quasithin.Background.A3FactsSchreierFinal
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Holds
public import CFSG.Quasithin.Vol2.Ch1EightTwoHubs
public import CFSG.Quasithin.Vol2.Ch1Sec3L42Inner
public import CFSG.Quasithin.Vol2.GoldschmidtJ4SevenWire

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

theorem a312ForSQTK_proved
    : A312ForSQTK :=
  A38c14.a312ForSQTK_of_residual A3Facts.a134ForSQTK A3Facts.schreierSQTK
    A38c17.a312ResidualRest2_holds.toRest3.toRest4.toRest10.toRest

theorem lemma128Two_proved
    : Lemma128Two :=
  Ch1Two.lemma128Two_of a312ForSQTK_proved

theorem lemma128Four_proved
    : Lemma128Four :=
  Ch1Four.lemma128Four_of a312ForSQTK_proved

theorem lemma139L42Inner_proved
    : Lemma139L42Inner :=
  L139L42.lemma139L42Inner_of (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved) a312ForSQTK_proved
      factJ4L42Inner_holds

end CFSG.Quasithin.H13

end
