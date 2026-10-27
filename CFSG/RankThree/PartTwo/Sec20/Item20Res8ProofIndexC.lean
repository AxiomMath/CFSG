module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res7ProofIndexN
import CFSG.RankThree.PartTwo.Sec20.Step2054Proof

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

theorem step2051IndexC_of (h187 : Sec18.Item187) (hO2 : Step189O2) : Step2051IndexC := by
  intro G _ _ A M L N c T hT hcase
  obtain ⟨n, hn, he, -⟩ := hcase
  have hle : M ⊓ Res6.cenK (kTwenty M c) ≤ N := fun q hq =>
    mem_of_centralizes_quotient h187 hO2 hT ⟨n, hn, he⟩ hq.1 hq.2.2
  rw [inf_of_le_left hle, Subgroup.relIndex_self]
  norm_num

end CFSG.RankThree.PartTwo.Sec20
