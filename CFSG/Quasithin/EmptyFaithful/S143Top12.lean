module

public import CFSG.Quasithin.EmptyFaithful.S143Top10
public import CFSG.Quasithin.EmptyFaithful.S143UF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

structure Inputs14316Twelve : Prop where
  h11 : StageLemma14111
  h113 : StageLemma14113
  h15 : Lemma14315
  h37 : A37ForSQTK
  h39 : A39ForSQTK
  list115 : Lemma115_3_List
  inspect : Lemma14320Inspect
  inspectW2 : Lemma14322InspectW2

theorem Inputs14316Twelve.toInputsTen
    (h : Inputs14316Twelve) : Inputs14316Ten :=
  { h11 := h.h11
    h113 := h.h113
    h15 := h.h15
    h37 := h.h37
    h39 := h.h39
    list115 := h.list115
    inspect := h.inspect
    fusion := lemma14322TailFusion_of_inspect2 h.inspectW2 }

end S143

theorem stageTheorem14316_of_inputs12
    (h : S143.Inputs14316Twelve) : StageTheorem14316 :=
  stageTheorem14316_of_inputs10 h.toInputsTen

end CFSG.Quasithin
