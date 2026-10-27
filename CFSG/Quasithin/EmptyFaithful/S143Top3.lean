module

public import CFSG.Quasithin.EmptyFaithful.S143Top
public import CFSG.Quasithin.EmptyFaithful.S143HD

public section

namespace CFSG.Quasithin

namespace S143

structure Inputs14316Three : Prop where
  h11 : StageLemma14111
  h113 : StageLemma14113
  h15 : Lemma14315
  h19four : Lemma14319Four
  h19ten : Lemma14319TenFiveSixSeven
  h20 : Lemma14320
  h21b : Lemma14321Two
  h22 : Lemma14322

theorem Inputs14316Three.toInputsTwo (h : Inputs14316Three) : Inputs14316Two :=
  { h11 := h.h11
    h113 := h.h113
    h15 := h.h15
    h19b := lemma14319Rest_of_parts h.h19four h.h19ten
    h20 := h.h20
    h21b := h.h21b
    h22 := h.h22 }

end S143

theorem stageTheorem14316_of_inputs3 (h : S143.Inputs14316Three) : StageTheorem14316 :=
  stageTheorem14316_of_inputs2 h.toInputsTwo

end CFSG.Quasithin
