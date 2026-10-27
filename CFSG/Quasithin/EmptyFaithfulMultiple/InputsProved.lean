module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs2
public import CFSG.Quasithin.Background.I4Recognition

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

theorem inputI41Two_holds
    : InputI41Two :=
  fun G _ _ hinv _ hz hC => CFSG.Quasithin.I4.lemma_I_4_1_two G hinv hz hC

end CFSG.Quasithin.EmptyFaithfulMultiple
