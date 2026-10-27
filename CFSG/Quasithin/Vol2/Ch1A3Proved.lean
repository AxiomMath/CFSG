module

public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal

public section

namespace CFSG.Quasithin

theorem a37ForSQTK_proved :
    A37ForSQTK :=
  a37ForSQTK_of_cat QuasithinUnique.Vol2Native.a37ForSQTKCat_proved

theorem a38ForSQTK_proved :
    A38ForSQTK :=
  a38ForSQTK_of_cat (QuasithinUnique.Vol2Native.a38ForSQTKCat_of_facts
    mult2Fact QuasithinUnique.Vol2Native.a134SQTKFactCat
    QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved
    QuasithinUnique.Vol2Native.a37ForSQTKCat_proved)

theorem a39ForSQTK_proved :
    A39ForSQTK :=
  a39ForSQTK_of_cat QuasithinUnique.Vol2Native.a39ForSQTKCat_proved

end CFSG.Quasithin
