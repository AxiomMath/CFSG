module

public import CFSG.Quasithin.MS93.S38EHolds
public import CFSG.Quasithin.MS93.S38EA
public import CFSG.Quasithin.MS93.S38Main
public import CFSG.Quasithin.MS93.S36Holds

public section

namespace CFSG.Quasithin.MS93

theorem s38_of_g2
    (hG2 : S38G2) : S38 :=
  s38_of s32_holds (S38E.s38End_holds_of_d6 S38E.d6Case_holds) hG2

theorem s36_of_g2
    (hG2 : S38G2) : S36 :=
  s36_of_s38 (s38_of_g2 hG2)

end CFSG.Quasithin.MS93
