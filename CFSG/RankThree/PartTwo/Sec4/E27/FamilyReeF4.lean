module

public import CFSG.RankThree.PartTwo.Sec4.E27.ReeF4Two
public import CFSG.RankThree.PartTwo.Sec4.E27.InnerRank
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27
open CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZ2 CFSG.Open
  CFSG.LieType.SeitzGeneration

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem seitz27_reeF4_of_plane
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (hP : FixPlaneGen (F4.reeGamma K a) 3) :
    Seitz27 (F4.reeGamma K a) := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  have : Finite (F4.reeGamma K a) := Subtype.finite
  refine seitz27_of_inner_outer (large_Ree_fixed_group_center_trivial a K hK)
    (hinner_of_rankLE2 fun E hE => ?_) (fieldAutData_reeF4_three ha hK) hP
  exact (CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma a K hK E hE).trans
    (by norm_num)

end CFSG.RankThree.PartTwo.Sec4.E27
