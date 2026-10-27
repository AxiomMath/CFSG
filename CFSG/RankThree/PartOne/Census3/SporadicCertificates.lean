module

public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.RankThree.PartTwo.Census.Sporadic.Co1
import CFSG.RankThree.PartTwo.Census.Sporadic.Fi23
public import CFSG.RankThree.PartTwo.Census.Sporadic.Co1Bridge
public import CFSG.Sporadic.Bridge.Fi23Surj

public section

namespace CFSG.RankThree.PartOne.Census3

open CFSG.Blueprint CFSG.QuasithinUnique.SQTK CFSG.RankThree.PartTwo.Census TauCeti

theorem excludedIndex_Co1 : ExcludedIndex (.sporadic .Co1) :=
  @excludedIndex_of_equiv (.sporadic .Co1) NativeSporadic.Co1 Units.instGroup
    (fun h => @nonempty_mulEquiv_Co1 h) 3 Nat.prime_three (by norm_num)
    four_le_localRank_three_Co1

theorem excludedIndex_Fi23 : ExcludedIndex (.sporadic .Fi23) :=
  @excludedIndex_of_equiv (.sporadic .Fi23) NativeSporadic.Fi23 Units.instGroup
    (fun _ => CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv.map MulEquiv.symm) 3 Nat.prime_three
    (by norm_num) four_le_localRank_three_Fi23

end CFSG.RankThree.PartOne.Census3
