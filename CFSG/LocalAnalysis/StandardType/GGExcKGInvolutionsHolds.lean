module

public import CFSG.LocalAnalysis.StandardType.GGExcKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGLatOrth
public import CFSG.LocalAnalysis.StandardType.GGExcKGInvolutionsF4
public import CFSG.LocalAnalysis.StandardType.GGExcKGInvolutionsE6
public import CFSG.LocalAnalysis.StandardType.GGExcKGInvolutionsE7
public import CFSG.LocalAnalysis.StandardType.GGExcKGInvolutionsE8
public import CFSG.LocalAnalysis.StandardType.GGExcKGInvolutionsTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section InvolutionsHolds


theorem ggExcKGInvolutions_holds : GGExcKGInvolutions ggASClass := by
  intro t n f ht G _ _ ψ hset s hs hs2
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact ggExcKGInvolutions_F4 n f G ψ hset s hs hs2
  · exact ggExcKGInvolutions_E6 n f G ψ hset s hs hs2
  · exact ggExcKGInvolutions_E7 n f G ψ hset s hs hs2
  · exact ggExcKGInvolutions_E8 n f G ψ hset s hs hs2
  · exact ggExcKGInvolutions_twistedE6 n f G ψ hset s hs hs2

end InvolutionsHolds

end CFSG.StandardType
