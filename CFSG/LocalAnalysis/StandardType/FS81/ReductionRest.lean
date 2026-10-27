module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalRows
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreHolds
public import CFSG.LocalAnalysis.StandardType.FS81.NotMonomial
public import CFSG.LocalAnalysis.StandardType.FS81.N6Main
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainExcl
public import CFSG.LocalAnalysis.StandardType.FS81.N7Fix
public import CFSG.LocalAnalysis.StandardType.FS81.N7N0
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameHolds
public import CFSG.LocalAnalysis.StandardType.FS81.D6Frame
public import CFSG.LocalAnalysis.StandardType.FS81.HoltEnd
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoinTBDefs

public section

namespace CFSG.StandardType.FrameRoute

namespace FS81

theorem fs81ThmACRankInput_of_rest (h : FS81ThmACRankRest) : FS81ThmACRankInput := by
  obtain ⟨h27, h3a⟩ := h
  have h1f : L1N7 :=
    l1N7_of_cases (l1N7Main_of_goldSylow goldExclusionSylow_of_certificates)
      l1N7Fix_holds l1N7N0_holds
  exact fs81ThmACRankInput_of_pieces fs81_L0CanonPosition l1Local_holds l1Fus42_holds
    l1OddCore_holds l1NotMonomial_holds l1N6_holds h1f l1E7_holds
    (l2ConstructY_of_rows l2ConstructYAt_D6_holds h27 E7Frame.l2ConstructYAt_E7_holds) h3a
    l3HoltEnd_holds

end FS81

theorem ggFrameRouteJoinTBInputs_of_rest (h : GGFrameRouteJoinTBRestInputs) :
    GGFrameRouteJoinTBInputs :=
  FS81.fs81ThmACRankInput_of_rest h

end CFSG.StandardType.FrameRoute

end
