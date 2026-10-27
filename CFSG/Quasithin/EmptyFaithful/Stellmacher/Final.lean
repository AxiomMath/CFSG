module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Frontier14
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Final

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

theorem F53.Stellmacher.hss35Orth_holds : F53.Stellmacher.Hss35Orth :=
  fun G _ _ H M S hA =>
    F53.Stellmacher.S35.hss35OrthAt_of hA (F53.Stellmacher.hss26A_holds G H M S hA)

theorem F53.Stellmacher.f53Dichotomy2_holds : F53Dichotomy2 :=
  F53.Stellmacher.f53Dichotomy2_of_hss35Orth F53.Stellmacher.hss35Orth_holds

end CFSG.Quasithin
