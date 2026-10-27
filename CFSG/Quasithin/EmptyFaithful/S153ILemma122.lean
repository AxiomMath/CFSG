module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved

public section

namespace CFSG.Quasithin

theorem lemma122A_of_native (h : CFSG.QuasithinUnique.Vol2Native.Lemma122A) : Lemma122A := by
  intro G _ _ hS hQ hna H L hH hL p hp hp2 hc hd
  exact h G hS hna (CFSG.QuasithinUnique.qtkeCore_of_cat hna hQ) H L hH hL p hp hp2 hc hd

theorem lemma122A_holds
        : Lemma122A :=
  lemma122A_of_native CFSG.QuasithinUnique.Vol2Native.lemma122A_proved

end CFSG.Quasithin
