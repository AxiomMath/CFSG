module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck156O2Main
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MAssembly3
public import CFSG.RankThree.PartTwo.Sec4.Item41ScopeProofAll

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck156

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14


theorem step156CQA5DO2R_holds
    : Step156CQA5DO2R := by
  obtain ⟨h45, h48, -, -, -, -, -, -, h134, -, -⟩ := Ronan148M.closedInputs
  exact step156CQA5DO2R_of h134 h48 h45 Sec4.Census.rank3II_4_4_of_griess_noItem41
    typeK156_holds Ronan148M.item143QS14_holds

section Faith


theorem step156CQA5DFaithR_of_item153
    (h153 : Item153MainR) : Step156CQA5DFaithR := by
  obtain ⟨-, h48, -, -, -, -, -, -, h134, -, h142⟩ := Ronan148M.closedInputs
  exact step156CQA5DFaithR_of_o2 h134 h48 h142 h153 step156CQA5DO2R_holds

end Faith

end CFSG.RankThree.PartTwo.Sec15.Liebeck156
