module

public import CFSG.Quasithin.H13.NQCoreP134Dich3
public import CFSG.Quasithin.H13.NQCoreP134OutThreeHolds
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddAbel

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.QuasithinUnique

theorem prop134Dich_holds :
    Prop134Dich :=
  prop134Dich_of_out Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved
    Vol2.Ch10.SecA.a38ForSQTKCat_proved outThreeFact_holds facts134Odd_outCyclic
    facts134Odd_outAbelian

theorem input137_holds :
    EmptyFaithfulMultiple.Input137 :=
  Thm137.input137_of_prop134Dich prop134Dich_holds

end CFSG.Quasithin.H13.NQCore
