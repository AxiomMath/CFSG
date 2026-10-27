module

public import CFSG.Quasithin.EmptyFaithful.S1421Q9Main
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.EmptyFaithful.S1421STC3Defs

public section

namespace CFSG.Quasithin

open CFSG.Open

theorem lemma14209Used_holds
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h128One : Lemma128One) (h128Two : Lemma128Two) (h128Four : Lemma128Four)
    (hL34 : Q9.L34Maximal) : Lemma14209Used :=
  fun G _ _ T M H K1 st hlt =>
    lemma14209Used_of_shape h37 h38 h39 h128One h128Two h128Four hL34 G T M H K1 st st.shape hlt

end CFSG.Quasithin
