module

public import CFSG.Quasithin.Vol2.GoldschmidtJ4SevenMain
public import CFSG.Quasithin.Vol2.GoldschmidtJ4SevenKG
public import CFSG.Quasithin.Vol2.GoldschmidtJ4SevenFact

public section

namespace CFSG.Quasithin.H13

theorem kgJ4SylowOvergroups_holds :
    KGInsp.KGJ4SylowOvergroups :=
  kgJ4SylowOvergroups_of_notReal j4SevenNotReal_holds

theorem factJ4L42Inner_holds :
    L139L42.FactJ4L42Inner :=
  factJ4L42Inner_of_notReal j4SevenNotReal_holds

end CFSG.Quasithin.H13
