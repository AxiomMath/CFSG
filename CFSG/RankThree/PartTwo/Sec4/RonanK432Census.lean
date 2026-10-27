module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Main
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowLargePrime
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowMcLON

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section Census

theorem list42_quotient_center {L : Type} [Group L] [Finite L] (hq : IsQuasisimple L)
    (hS : SectionFourHyp L) : Census.List42 (L ⧸ Subgroup.center L) := by
  have hGA := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have h1 := Item41Narrow.item4_1LargePrime_of_griess hGA
  have h2 := Item41Narrow.item4_1ThreeCover_of_griess hGA
  have hS' := Item41Narrow.sectionFourHyp_quotient_center h1 h2 hS hq
  exact Census.rank3II_4_2 (L ⧸ Subgroup.center L) hS' hq.2.1 hq.2.2

theorem k432InnerThree_of_rows (R : K432Rows) : K432InnerThree :=
  k432InnerThree_of_goodRow fun _ _ _ hq hS =>
    R.goodRow_of_list42 hq.2.1 hq.2.2 (list42_quotient_center hq hS)

theorem k432List_of_rows (R : K432Rows) : K432List :=
  k432List_of_goodRow fun _ _ _ hq hS =>
    R.goodRow_of_list42 hq.2.1 hq.2.2 (list42_quotient_center hq hS)

end Census

end CFSG.RankThree.PartTwo.Sec4.RonanK432
