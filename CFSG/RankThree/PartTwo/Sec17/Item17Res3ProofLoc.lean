module

import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
public import CFSG.RankThree.PartTwo.Sec15.Notation
public import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofJ2

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped Pointwise

namespace Proof17Res3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_pow_three_mem {L : Subgroup G} {x : G} (hx : Nat.Coprime 3 (orderOf x))
    (hx3 : x ^ 3 ∈ L) : x ∈ L := by
  have hmem : x ∈ Subgroup.zpowers (x ^ 3) := mem_zpowers_pow_iff.mpr hx
  exact (Subgroup.zpowers_le.mpr hx3) hmem

end Proof17Res3

end CFSG.RankThree.PartTwo.Sec17
