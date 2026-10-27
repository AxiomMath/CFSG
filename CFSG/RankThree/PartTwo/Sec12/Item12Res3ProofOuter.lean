module

public import CFSG.RankThree.PartTwo.Sec12.Item128StepsProofAInL
import CFSG.RankThree.PartTwo.Sec12.Item12Res3ProofPGLMain

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lBarA)

theorem ks128SLAInLOuter_of_items
    (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves) :
    KS128SLAInLOuter := by
  intro G _ _ A c L hstd hAE hSL a ha haB K hK hcK hconf
  rcases hconf with ⟨-, -, x, hxA, -, hx⟩ | hm12
  · exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      Res3Proof.mem_of_pgl hstd hAE hSL ha haB hK hcK hxA hx
  · obtain ⟨φ⟩ := hm12.1
    exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      Res3Proof.mem_of_m12 h45 hK2 hstd hAE hSL ha haB hK hcK φ

section Unconditional

theorem ks128SLAInLOuter
    : KS128SLAInLOuter :=
  ks128SLAInLOuter_of_items Sec4.rank3II_4_5 KFacts.ks12NormalizerMoves

theorem ks128NotHJFree
    : KS128NotHJFree :=
  ks128NotHJFree_of_outer ks128SLAInLOuter

end Unconditional

end CFSG.RankThree.PartTwo.Sec12
