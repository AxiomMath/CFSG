module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SMain
public import CFSG.RankThree.PartTwo.Sec13.Item137ProofMain
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MAssembly
public import CFSG.RankThree.PartTwo.Late.Item2011
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan137H

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13


theorem item137InvertPGL_holds
    : Item137InvertPGL :=
  Ronan138S.item137InvertPGL_of rank3II_13_1_holds sporadicModels131
    Sec4.Sporadic.rank3II_4_14_local KFacts.ks18M12

theorem item137_holds
    : Item137 := by
  obtain ⟨h45, h48, -, h422, -, -, -, h131, h134, h133, -⟩ := Sec14.Ronan148M.closedInputs
  exact item137_of_items h131 h422 h45 h133 h134 h48
    (Late.item13Setup_of (item13SetupAt_of h422 h45)) item137InvertPGL_holds

end CFSG.RankThree.PartTwo.Sec13.Ronan137H
