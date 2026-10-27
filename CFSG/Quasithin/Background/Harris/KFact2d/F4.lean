module

public import CFSG.Quasithin.Background.Harris.KFact2d.F4L3
public import CFSG.Quasithin.Background.Harris.KFact2d.F4U3

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d


theorem f4_holds : F4Stmt := by
  intro E _ _ p hp hp2 hperf hodd hL v hv hnot c hc
  rcases hL with ⟨hp4, hU⟩ | ⟨_, hL⟩
  · exact f4_psu E p hp hp4 hperf hodd hU v hv hnot c hc
  · exact f4_psl E p hp hp2 hperf hodd hL v hv hnot c hc

end CFSG.Quasithin.Background.Harris.KFact2d
