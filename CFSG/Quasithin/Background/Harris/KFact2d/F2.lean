module

public import CFSG.Quasithin.Background.Harris.KFact2d.ModelL3
public import CFSG.Quasithin.Background.Harris.KFact2d.ModelU3

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

theorem f2_holds : F2Stmt := by
  intro X _ _ K S p hp hp11 hK hS
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hK with ⟨hp4, hL⟩ | ⟨hp4, hL⟩
  · exact f2_psu hp4 hp11 hL hS
  · exact f2_psl hp4 hp11 hL hS

end CFSG.Quasithin.Background.Harris.KFact2d
