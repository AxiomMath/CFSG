module

public import CFSG.Quasithin.Vol2.Ch1EightTwo
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Lt
public import CFSG.Quasithin.H13.NQCatLemma128One
public import CFSG.Quasithin.H13.A7Nat1236Final

public section

namespace CFSG.Quasithin.Ch1Two

open CFSG.Quasithin CFSG.QuasithinUnique

theorem lemma128TwoAS_of_inputs
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h312 : A312ForSQTK) (h128 : Lemma128One) :
    H13.Lemma128TwoAS :=
  lemma128TwoAS_form_of_inputs h37 h38 h312 h128

theorem lemma128TwoAS_of
    (h312 : A312ForSQTK) : H13.Lemma128TwoAS :=
  lemma128TwoAS_of_inputs (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved)
    (a38ForSQTK_of_cat H13.A7.a38ForSQTKCat_holds) h312 H13.NQCat.lemma128One_holds

theorem lemma128Two_of
    (h312 : A312ForSQTK) : Lemma128Two :=
  (lemma128TwoAS_of h312).toLemma128Two

end CFSG.Quasithin.Ch1Two
