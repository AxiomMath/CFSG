module

public import CFSG.Quasithin.EmptyFaithful.S14620E
public import CFSG.Quasithin.EmptyFaithful.S14620H

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

theorem stage14620_of_reduced_inputs
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (i2 : Input14620M22) (i3 : L5Core)
    (i5 : Input14620Rank2) (i6 : Input14620Bender) : Stage14620 :=
  stage14620_of_named_inputs h37 h38 hD36 hD37 hD321 hI5 hD310 hD391 hI4 input14620A7 i2
    (input14620L45_of_l5Core i3) input14620Borel i5 i6 input14620K0

end CFSG.Quasithin
