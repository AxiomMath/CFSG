module

public import CFSG.RankThree.GF2n.Smith81.S81KElem
public import CFSG.RankThree.GF2n.Smith81.S81KLead

public section

namespace CFSG.RankThree.GF2n.Smith81.SK

section Lead


theorem leadRootsBound_holds : LeadRootsBoundStatement :=
  fun _ _ _ _ A hA hc => card_le_pow_leadRoots A hA hc

end Lead


theorem elemAbelianBoundE4_holds : ElemAbelianBoundE4 :=
  elemAbelianBoundE4_of_lead leadRootsBound_holds

end CFSG.RankThree.GF2n.Smith81.SK
