module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Prop134E9Proof

public section

namespace CFSG.Quasithin.P134

open CFSG.QuasithinUnique.Vol2Native

theorem theoremCSimple
    : TheoremCSimple := fun S _ _ _ hnab hSQTK =>
  CFSG.Milestones.cl_lit_sqtk_simple_list_simple S hnab hSQTK

theorem prop134E9He_of_facts
    (h36 : A36CoreForSQTKCat) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (hF : Facts134E9He) :
    CFSG.Quasithin.EmptyFaithfulMultiple.Prop134E9He :=
  CFSG.Quasithin.EmptyFaithfulMultiple.prop134E9He_of h36 h37 h38 theoremCSimple hF

end CFSG.Quasithin.P134
