module

public import CFSG.RankThree.PartTwo.Sec15.Item1523Proof
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta
import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofCover
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow1523K

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.Proof171Steps

variable {G : Type} [Group G] [Finite G]

theorem k1523_le_centralizer (A : Subgroup G) (d : G) :
    k1523 A d ≤ Subgroup.centralizer ({d} : Set G) :=
  (oPrimeResidualOf_le_self 3 _).trans (delta_le _)

theorem k1523_eq_oPrimeResidualOf (A : Subgroup G) (d : G) :
    k1523 A d = oPrimeResidualOf 3 (k1523 A d) :=
  (Proof1515Res.oRes3_idem _).symm

end CFSG.RankThree.PartTwo.Sec15.Sylow1523K
