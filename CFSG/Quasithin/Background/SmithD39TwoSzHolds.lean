module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34D38
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D35Holds
public import CFSG.Quasithin.Vol2.Ch10SecQ1Facts
public import CFSG.Quasithin.Background.SmithD37Main
public import CFSG.Quasithin.Background.SmithD36THolds
public import CFSG.Quasithin.Background.SmithB45Holds

public section

namespace CFSG.Quasithin.SmithD39Two

open CFSG.Quasithin

theorem d36c_holds :
    D36c :=
  d36c_of_named_inputs_tight H13.d35_proved d36QhatGluedTight_holds d36A38_holds
    (d3L38_of_a38 d3A38_holds)

theorem d38Top_holds :
    D38Top :=
  H13.d38Top_of Vol2.Ch10.SecA.a38ForSQTKCat_proved H13.d35_proved d36c_holds d37_holds
    asB45_holds asA21SQTKSection Vol2.Ch10.SecA.facts10_1_holds

end CFSG.Quasithin.SmithD39Two
