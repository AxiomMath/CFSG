module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs2
public import CFSG.Quasithin.EmptyFaithful.S1413
public import CFSG.Quasithin.Vol2.Ch1Unique
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.Quasithin.Background.C1PackSolvFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native39
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporSchreier
public import CFSG.Quasithin.Background.KnownMultTypes

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ComponentClassification.SporadicSchreierDispatch (SporadicSchreierCase)

theorem a39ForSQTKCat_of_J4
    (hJ4 : SporadicSchreierCase .J4) : Vol2Native.A39ForSQTKCat :=
  Vol2Native.a39ForSQTKCat_of_facts (Vol2Native.schreierFactListCat_of_J4 hJ4)
    Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved
    (Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)

theorem input1413_of_J4
    (hJ4 : SporadicSchreierCase .J4) : Input1413 :=
  stageLemma1413_of_a39 (a39ForSQTK_of_cat (a39ForSQTKCat_of_J4 hJ4))

theorem input127Three_of_J4
    (hJ4 : SporadicSchreierCase .J4) : Input127Three :=
  fun _ _ _ _ hs hnab hK hT _ hL =>
    lemma_1_2_7_three hK hs hnab (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved)
      (a38ForSQTK_of_cat (Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact
        Vol2Native.a134SQTKFactCat Vol2Native.a36CoreForSQTKCat_proved
        Vol2Native.a37ForSQTKCat_proved))
      (a39ForSQTK_of_cat (a39ForSQTKCat_of_J4 hJ4)) hT hL

theorem inputGNC128Solv_holds : InputGNC128Solv := gNCampbellC128Solv

end CFSG.Quasithin.EmptyFaithfulMultiple
