module

public import CFSG.Quasithin.EmptyFaithful.S143Top3
public import CFSG.Quasithin.EmptyFaithful.S143IG
public import CFSG.Quasithin.EmptyFaithful.S143JB

public section

namespace CFSG.Quasithin

namespace S143

structure Inputs14316Four : Prop where
  h11 : StageLemma14111
  h113 : StageLemma14113
  h15 : Lemma14315
  h19four : Lemma14319Four
  h19rest : Lemma14319SixRestSeven
  h20 : Lemma14320
  h22 : Lemma14322

theorem Inputs14316Four.toInputsThree (h : Inputs14316Four) : Inputs14316Three :=
  { h11 := h.h11
    h113 := h.h113
    h15 := h.h15
    h19four := h.h19four
    h19ten := lemma14319TenFiveSixSeven_of_rest h.h19rest
    h20 := h.h20
    h21b := lemma_14_3_21_two
    h22 := h.h22 }

end S143

theorem stageTheorem14316_of_inputs4 (h : S143.Inputs14316Four) : StageTheorem14316 :=
  stageTheorem14316_of_inputs3 h.toInputsThree

end CFSG.Quasithin
