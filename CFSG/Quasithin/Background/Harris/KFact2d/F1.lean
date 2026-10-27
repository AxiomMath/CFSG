module

public import CFSG.Quasithin.Background.Harris.KFact2d.F1L3
public import CFSG.Quasithin.Background.Harris.KFact2d.F1U3

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

theorem f1_holds : F1Stmt := by
  intro X _ _ K S p hp _ hK hS E hE hES hSN
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hK with ⟨hp4, hL⟩ | ⟨hp4, hL⟩
  · exact f1_psu hp4 hL hS E hE hES hSN
  · exact f1_psl hp4 hL hS E hE hES hSN

end CFSG.Quasithin.Background.Harris.KFact2d
