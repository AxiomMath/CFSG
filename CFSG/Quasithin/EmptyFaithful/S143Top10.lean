module

public import CFSG.Quasithin.EmptyFaithful.S143Top9
public import CFSG.Quasithin.EmptyFaithful.S143RC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

structure Inputs14316Ten : Prop where
  h11 : StageLemma14111
  h113 : StageLemma14113
  h15 : Lemma14315
  h37 : A37ForSQTK
  h39 : A39ForSQTK
  list115 : Lemma115_3_List
  inspect : Lemma14320Inspect
  fusion : Lemma14322TailFusion

theorem Inputs14316Ten.toInputsNine
    (h : Inputs14316Ten) : Inputs14316Nine :=
  { h11 := h.h11
    h113 := h.h113
    h15 := h.h15
    h37 := h.h37
    h39 := h.h39
    list115 := h.list115
    inspect := h.inspect
    tail := lemma14322Tail_of_fusion h.fusion }

end S143

theorem stageTheorem14316_of_inputs10
    (h : S143.Inputs14316Ten) : StageTheorem14316 :=
  stageTheorem14316_of_inputs9 h.toInputsNine

end CFSG.Quasithin
