module

public import CFSG.RankThree.PartOne.N143.Weyl613List
public import CFSG.RankThree.PartOne.N143.Weyl613Bridge
public import CFSG.RankThree.PartOne.N143.Item613IdxA
public import CFSG.RankThree.PartOne.N143.Item613IdxB
public import CFSG.RankThree.PartOne.N143.Item613IdxC
public import CFSG.RankThree.PartOne.N143X.EvenRankTwoHolds
public import CFSG.RankThree.PartOne.N143.JFactsOf
public import CFSG.RankThree.PartOne.KFOUT3.LemmaK2
public import CFSG.RankThree.PartOne.KFOUT3.Lemma42
public import CFSG.RankThree.PartOne.KFOUT3.LemmaB
import CFSG.RankThree.PartOne.KF.R1Final

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem item613ListIdx_holds :
    Item613ListIdx := by
  intro X _ _ hs h
  rcases h with h | h | h | h | h | h | h | h | h
  · exact item613Idx_item1 X hs h
  · exact item613Idx_item2 X hs h
  · exact item613Idx_item3 X hs h
  · exact item613Idx_item4 X hs h
  · exact item613Idx_item5 X hs h
  · exact item613Idx_item6 X hs h
  · exact fun _ _ _ _ _ _ _ => Or.inl h
  · exact fun _ _ _ _ _ _ _ => Or.inr (Or.inl h)
  · exact fun _ _ _ _ _ _ _ => Or.inr (Or.inr h)

theorem kf64wSimpleSmall_holds :
    KF64WSimpleSmall :=
  kf64wSimple_of_small N143X.evenRankTwoExceptionalNoPCube_holds

theorem kf64wSimpleList_holds :
    KF64WSimpleList :=
  kf64wSimpleList_of_small kf64wSimpleSmall_holds (fun _ _ h => evenLieTypeSmall_of_item789 h)

theorem node143Comm_of_list
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchreier : SchreierFor InCatalog) (h107 : InSec10Seven) (h109 : InSec10Nine)
    (h122 : Node122) (hpair : KF134Pair) (hB2 : Node143CommB2Sup) (hSLB : SectionListBound) :
    Node143Comm :=
  node143Comm_of_kfacts_sup_gen (Q := ListEvenQ) hGA hSchreier kf123Row1 h107 h109 h122 hpair
    KFOUT3.jLemmaF KFOUT3.jLemmaK2 KFOUT3.jLemma42 (KFOUT3.jLemmaB_holds hGA) hB2
    (kf64wWith_listEven hSLB kf64wSimpleList_holds) (item613With_listEven hSLB item613ListIdx_holds)

end CFSG.RankThree.PartOne.N143
