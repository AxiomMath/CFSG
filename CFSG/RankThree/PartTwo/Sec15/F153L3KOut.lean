module

public import CFSG.RankThree.PartTwo.Sec15.F153L3KOutBig
public import CFSG.RankThree.PartTwo.Sec15.F153L3KOutU
public import CFSG.RankThree.PartTwo.Sec15.F153L3KOutL32

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K

open CFSG.RankThree.PartTwo.Sec15.F153L3K.Out

theorem kFactL3NoOuterOffender_holds :
    CFSG.RankThree.PartTwo.Sec15.F153L3C2.KFactL3NoOuterOffender := by
  intro T _ f hf hT
  have hT' : Nonempty (T ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 f)) ∨
      (2 < 2 ^ f ∧ Nonempty (T ≃* CFSG.Assembly.RankThreeEven.projSU 3 2 f)) := hT
  refine noOuterFFOffender_of_noOuterIrr (outTwoRank_of_isLThreeEpsAt hf hT') ?_
  rcases hT' with hL | ⟨h2f, hU⟩
  · rcases Nat.lt_or_ge f 2 with h1 | h2
    · have hf1 : f = 1 := by omega
      subst hf1
      exact noOuterIrr_L32 hL
    · exact noOuterIrr_L3big h2 hL
  · exact noOuterIrr_U3 h2f hU

end CFSG.RankThree.PartTwo.Sec15.F153L3K
