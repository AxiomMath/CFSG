module

public import CFSG.Quasithin.Background.Harris.KFact2d.Defs

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

theorem f5_of_primes (h3 : StarStmtFor fun q => q = 3) (h5 : StarStmtFor fun q => q = 5)
    (h7 : StarStmtFor fun q => q = 7) : F5Stmt := by
  intro X _ _ K T M V p hp hc hV hVT hTV hA
  rcases hp with rfl | rfl | rfl
  · exact h3 X K T M V 3 rfl hc hV hVT hTV hA
  · exact h5 X K T M V 5 rfl hc hV hVT hTV hA
  · exact h7 X K T M V 7 rfl hc hV hVT hTV hA

end CFSG.Quasithin.Background.Harris.KFact2d
