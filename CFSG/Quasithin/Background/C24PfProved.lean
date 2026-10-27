module

public import CFSG.Quasithin.Background.C24PfF
public import CFSG.Quasithin.Background.Asc82Holds
public import CFSG.Quasithin.Vol2.Ch1A3Proved

public section

namespace CFSG.Quasithin.C24Pf

theorem asc24TwoChar_proved :
    ∀ (G : Type) [Group G] [Finite G], ASC24TwoChar G :=
  fun _ _ _ => asc24TwoChar_of asc82Thm2_holds a37ForSQTK_proved a38ForSQTK_proved

end CFSG.Quasithin.C24Pf
