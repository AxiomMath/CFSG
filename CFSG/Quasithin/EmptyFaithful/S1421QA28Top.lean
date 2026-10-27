module

public import CFSG.Quasithin.EmptyFaithful.S1421QA28Main
public import CFSG.Quasithin.EmptyFaithful.S1421QA28Lie
public import CFSG.Quasithin.EmptyFaithful.S1421QA18Order
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.Quasithin

namespace QA28

theorem lemma14218KcEq_of_a312_legacyBare
    (h312 : A312ForSQTK) : Lemma14218KcEqLegacyBare :=
  lemma14218KcEq_of_inputs_legacyBare h312 d4Order_holds rank2TwoPart_holds

theorem lemma14218Normal_of_a312_legacyBare
    (h312 : A312ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) : Lemma14218NormalLegacyBare :=
  S1421QA18.lemma14218Normal_of_kcEq_legacyBare h37 h38 h39 (lemma14218KcEq_of_a312_legacyBare h312)

end QA28

end CFSG.Quasithin
