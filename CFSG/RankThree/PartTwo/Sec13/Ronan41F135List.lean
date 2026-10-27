module

public import CFSG.RankThree.PartTwo.Sec13.Ronan41F135ListDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Ronan41SectionList42
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Sec

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section List

theorem componentList42_holds : ComponentList42 := by
  intro G _ _ M hM R _ J hJ
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.1.2.1
  exact Sec4.Census.list42_of_simple_section hM (J.comap (QuotientGroup.mk' R)) hJ.1.2.2
    (r5f_map R J) (r5f_map_surjective R J)

end List

end CFSG.RankThree.PartTwo.Sec13.F135Last
