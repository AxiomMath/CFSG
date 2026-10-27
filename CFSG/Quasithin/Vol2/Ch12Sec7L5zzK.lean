module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zzJ
public import CFSG.Quasithin.Vol2.Ch8Sec2KGCover
public import CFSG.Quasithin.Background.KG82CoverE16

public section

namespace CFSG.Quasithin.H13

theorem l34E16Parabolic_holds :
    L34E16Parabolic :=
  fun _ _ _ h A hc hs hA => CFSG.Quasithin.H.L34Cov.exists_parabolic_of_e16 h A hc hs hA

theorem l34CoverFact_holds :
    L34CoverFact :=
  l34CoverFact_of kg82CoverL34_holds l34E16Parabolic_holds

end CFSG.Quasithin.H13
