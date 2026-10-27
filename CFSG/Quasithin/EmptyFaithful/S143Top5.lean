module

public import CFSG.Quasithin.EmptyFaithful.S143Top4
public import CFSG.Quasithin.EmptyFaithful.S143KO

public section

namespace CFSG.Quasithin

namespace S143

structure Inputs14316Five : Prop where
  h11 : StageLemma14111
  h113 : StageLemma14113
  h15 : Lemma14315
  h19rest : Lemma14319SixRestSeven
  h20 : Lemma14320
  h22 : Lemma14322

theorem Inputs14316Five.toInputsFour (h : Inputs14316Five) : Inputs14316Four :=
  { h11 := h.h11
    h113 := h.h113
    h15 := h.h15
    h19four := lemma_14_3_19_four
    h19rest := h.h19rest
    h20 := h.h20
    h22 := h.h22 }

end S143

theorem stageTheorem14316_of_inputs5 (h : S143.Inputs14316Five) : StageTheorem14316 :=
  stageTheorem14316_of_inputs4 h.toInputsFour

end CFSG.Quasithin
