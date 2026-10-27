module

public import CFSG.RankThree.PartTwo.Sec19.F194Item316X
public import CFSG.Milestones.CL_LIT_GH74_sectional_two_rank_four
public import CFSG.Adapters.CatalogAgree
import CFSG.Milestones.CLS_low_two_rank_classification
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NinePair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.ComponentClassification.UFrontierCoreBranches
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec19

theorem sectionalTwoRankFourCatalog_holds :
    SectionalTwoRankFourCatalog := by
  intro G _ _ hsimple hnonab _ _ hsect
  haveI : IsSimpleGroup G := hsimple
  refine CFSG.Open.QTFaithfulEmptyTauCeti.inCatalog_of_catalog G ?_
  rcases le_or_gt (CFSG.Open.twoRank G) 2 with hr | hr
  · refine CFSG.Milestones.cls_low_two_rank_classification G hnonab ?_ hr
    by_contra hodd
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr
      (CFSG.Milestones.odd_order_solvable (Nat.not_even_iff_odd.mp hodd)) a b)
  · exact CFSG.ComponentClassification.UFrontier.catalog_of_gh74
      (fun G _ _ _ hnonab hrank hsect =>
        CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models G hnonab hrank hsect)
      hnonab (by omega) hsect

end CFSG.RankThree.PartTwo.Sec19
