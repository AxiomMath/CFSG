module

public import CFSG.RankThree.PartOne.KS.ONPwSound
public import CFSG.Sporadic.Schreier.ONLocalOrders

public section

namespace CFSG.RankThree.PartOne.ONPw

open CFSG.ONSchreier CFSG.ONSchreier.Native

@[expose] noncomputable def concreteEnv :
    Env where
  evalS := CFSG.ONSchreier.evalS
  prep := fun {_} hw => prep_wordArr hw
  Pv := Pv
  L := onL
  L_le := closure_evalList_le _
  L_closure := rfl
  sep := fun g hg h hh H =>
    eq_of_three hg hh (H ⟨0, by norm_num⟩ (by simp [baseA]))
      (H ⟨227759, by norm_num⟩ (by simp [baseA])) (H ⟨100817, by norm_num⟩ (by simp [baseA]))

end CFSG.RankThree.PartOne.ONPw
