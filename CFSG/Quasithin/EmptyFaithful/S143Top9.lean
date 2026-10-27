module

public import CFSG.Quasithin.EmptyFaithful.S143Top8
public import CFSG.Quasithin.EmptyFaithful.S143PC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

structure Inputs14316Nine : Prop where
  h11 : StageLemma14111
  h113 : StageLemma14113
  h15 : Lemma14315
  h37 : A37ForSQTK
  h39 : A39ForSQTK
  list115 : Lemma115_3_List
  inspect : Lemma14320Inspect
  tail : Lemma14322Tail

theorem Inputs14316Nine.toInputsEight
    (h : Inputs14316Nine) : Inputs14316Eight :=
  { h11 := h.h11
    h113 := h.h113
    h15 := h.h15
    h37 := h.h37
    h39 := h.h39
    list115 := h.list115
    inspect := h.inspect
    h22 := lemma_14_3_22_of_tail h.tail }

end S143

theorem stageTheorem14316_of_inputs9
    (h : S143.Inputs14316Nine) : StageTheorem14316 :=
  stageTheorem14316_of_inputs8 h.toInputsEight

end CFSG.Quasithin
