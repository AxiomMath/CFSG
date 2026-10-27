module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.Census.Sporadic.B

public section

namespace Certificates

theorem certificate8152 : ∀ [Finite CFSG.Blueprint.NativeSporadic.B],
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 CFSG.Blueprint.NativeSporadic.B :=
  CFSG.RankThree.PartTwo.Census.four_le_localRank_three_B

end Certificates
