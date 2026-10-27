module

public import CFSG.Quasithin.EmptyFaithful.S143Final
public import CFSG.Quasithin.EmptyFaithful.S143EH
public import CFSG.Quasithin.EmptyFaithful.S143FF
public import CFSG.Quasithin.EmptyFaithful.S143FK

public section

namespace CFSG.Quasithin

namespace S143

structure Inputs14316Two : Prop where
  h11 : StageLemma14111
  h113 : StageLemma14113
  h15 : Lemma14315
  h19b : Lemma14319Rest
  h20 : Lemma14320
  h21b : Lemma14321Two
  h22 : Lemma14322

theorem Inputs14316Two.toInputs (h : Inputs14316Two) : Inputs14316 :=
  { h11 := h.h11
    h113 := h.h113
    h15 := h.h15
    h18a := lemma_14_3_18_a
    h18b := lemma_14_3_18_b
    h18c := lemma_14_3_18_c
    h19b := h.h19b
    h20 := h.h20
    h21b := h.h21b
    h22 := h.h22 }

end S143

theorem stageTheorem14316_of_inputs2 (h : S143.Inputs14316Two) : StageTheorem14316 :=
  stageTheorem14316_of_inputs h.toInputs

end CFSG.Quasithin
