module

public import CFSG.Quasithin.Vol2.Ch3B513NC1All
public import CFSG.Quasithin.Vol2.Ch3B513NC3
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51

public section

namespace CFSG.Quasithin.B513N


theorem b513Nonsolvable_holds
    : B513Nonsolvable :=
  b513Nonsolvable_of_cases asB56_holds (case1_of_b42 asA21SQTKSection asB42_holds) case3_holds

end CFSG.Quasithin.B513N
