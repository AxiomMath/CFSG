module

public import CFSG.Quasithin.EmptyFaithful.S143Top7
public import CFSG.Quasithin.EmptyFaithful.S143NO

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

structure Inputs14316Eight : Prop where
  h11 : StageLemma14111
  h113 : StageLemma14113
  h15 : Lemma14315
  h37 : A37ForSQTK
  h39 : A39ForSQTK
  list115 : Lemma115_3_List
  inspect : Lemma14320Inspect
  h22 : Lemma14322

theorem Inputs14316Eight.toInputsSeven
    (h : Inputs14316Eight) : Inputs14316Seven :=
  { h11 := h.h11
    h113 := h.h113
    h15 := h.h15
    h20 := lemma_14_3_20_of_inputs h.h37 h.h39 h.list115 h.inspect
    h22 := h.h22 }

end S143

theorem stageTheorem14316_of_inputs8
    (h : S143.Inputs14316Eight) : StageTheorem14316 :=
  stageTheorem14316_of_inputs7 h.toInputsSeven

end CFSG.Quasithin
