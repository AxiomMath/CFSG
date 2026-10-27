module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Holds
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowTits
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowOmega
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowF4
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowD4

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint

set_option linter.unusedSectionVars false

section Final

theorem k432OpenRows : K432OpenRows where
  seven_D4 := rowOf_trialityD4
  seven_Tits := fun ht => listRowOf_tits_of_cert ht
  eight_OmegaPlus := rowOf_omegaPlus
  eight_F4 := listRowOf_f4_two_of_cert

theorem k432InnerThree_holds : K432InnerThree :=
  k432InnerThree_of_openRows k432OpenRows

theorem k432List_holds : K432List :=
  k432List_of_openRows k432OpenRows

end Final

end CFSG.RankThree.PartTwo.Sec4.RonanK432
