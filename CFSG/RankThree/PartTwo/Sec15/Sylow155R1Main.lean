module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidDefs
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Mid
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidL2Solv
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidL2Fix
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidL3Solv
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidL3Fix
import CFSG.RankThree.PartTwo.KFacts.KS44Sz
import CFSG.LocalAnalysis.UniquenessCase.UC1K45SzAut
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

section Certified

theorem step155HostE0WRes1Type_mid
    (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) (h142 : Sec14.Concl142S14) (h1444 : Sec14.Item1444S14) :
    Step155HostE0WRes1Type Res1MidType :=
  step155HostE0WRes1Type_of_autSolv_autFix h1 h2 h43 hin h143 h142 h1444 KFacts.kpSz
    CFSG.LocalAnalysis.UniquenessCase.UCK.szOrder3Aut_holds fun _ _ _ _ hY => by
      rcases hY with ⟨n, hn6, hn4, ⟨e⟩⟩ | ⟨n, -, hnodd, ⟨e⟩⟩
      · exact ⟨Res1AutSolv.of_mulEquiv e (res1AutSolv_projSL_two (by omega)),
          Res1AutFix.of_mulEquiv e (res1AutFix_projSL_two hn4)⟩
      · exact ⟨Res1AutSolv.of_mulEquiv e (res1AutSolv_projSL_three hnodd),
          Res1AutFix.of_mulEquiv e (res1AutFix_projSL_three hnodd)⟩

end Certified

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
