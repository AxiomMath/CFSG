module

public import CFSG.Quasithin.EmptyFaithful.S1421QA19Data
public import CFSG.Quasithin.EmptyFaithful.S1421QA19J4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem core3QuasiSmall_of_inputs
    (hF : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h2 : Lemma14215Step2) (h209 : Lemma14209Used) (h1284 : Lemma128Four)
    (hL34 : Q9.L34Maximal) : Core3QuasiSmallLe ∧ Core3QuasiSmallU :=
  ⟨core3QuasiSmallLe_of_parts hF h36 h37 h38 h39 h2 h209 h1284 core3SmallData_holds
      (QA19.core3KThree_of_inputs hF h36 h38 core3SmallData_holds QA19.core3CentData_holds),
    QA19.core3QuasiSmallU_of_inputs hF h36 h38 core3SmallData_holds QA19.core3CentData_holds
      (QA19.core3J4ShapeThree_of_inputs hF h36 h37 h38 h39 core3SmallData_holds h1284 hL34)⟩

end CFSG.Quasithin
