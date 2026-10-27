module

public import CFSG.LocalAnalysis.StandardType.GGFieldTwoCornerLeavesDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOne3Holds

public section

namespace CFSG.StandardType

theorem ggFieldTwoCornerNoSL28_of_leaves
    (hSmall : S2MathAs3_1615.corner1584_small_labels) (hConn : S2MathAs3_1615.corner1584_connected)
    (hSplit : S2MathAs3_1615.corner1584_split_lift) (hRem : GGCornerRemainingTypes)
    (hE6 : GGCornerE6) (hNon : S2MathAs3_1615.corner1584_nonsplit_shape) :
    GGFieldTwoCornerNoSL28 :=
  ggFieldTwoCornerNoSL28_of_strong
    (S2MathAs3_1615.corner1615Assembly_holds hSmall hConn (fun _ => hRem) (fun _ => hE6) hSplit
      hNon)

end CFSG.StandardType

end
