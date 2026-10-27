module

public import CFSG.Quasithin.Background.Harris.KFact2d.Reduction
public import CFSG.Quasithin.Background.Harris.KFact2d.Star
public import CFSG.Quasithin.Background.Harris.KFact2d.F2
public import CFSG.Quasithin.Background.Harris.KFact2d.F3
public import CFSG.Quasithin.Background.Harris.KFact2d.F4
public import CFSG.Quasithin.Background.Harris.KFact2d.F5Combine
public import CFSG.Quasithin.Background.Harris.KFact2d.F5Three
public import CFSG.Quasithin.Background.Harris.KFact2d.F5Five
public import CFSG.Quasithin.Background.Harris.KFact2d.F5Seven

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d


theorem kfact2dAtoms_holds : CFSG.Quasithin.Gap6R2.KFact2dAtoms :=
  kfact2dAtoms_of (starStmt_of f1_holds f2_holds f3_holds (f5_of_primes f5_three f5_five f5_seven))
      f1_holds f4_holds

end CFSG.Quasithin.Background.Harris.KFact2d
