module

public import CFSG.LocalAnalysis.StandardType.GGE78LocalRank
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs

public section

namespace CFSG.StandardType

theorem ggE78TwoLocalRankSix_holds :
    GGE78TwoLocalRankSix := by
  intro H _ _ hP lab hΛ htag hlab
  have h := ggE78LocalRankThree_holds H lab hΛ htag hlab (Group.isPerfect_def.mp hP)
  exact le_trans (Nat.le_add_right 6 _) h

end CFSG.StandardType

end
