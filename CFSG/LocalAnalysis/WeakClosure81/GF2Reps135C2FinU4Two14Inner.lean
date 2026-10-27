module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Rank
public import CFSG.HardMathSupport.U4FF.Disp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.RankThreeUC
open CFSG.HardMathSupport.U4FF (disp u4RankDichotomySix_holds)

theorem finU4_inner_disp_ge
    {S : Type} [CommGroup S] [Finite S] [Fact (∀ s : S, s * s = 1)]
    {L : Subgroup (MulAut S)} (hL : IsU4Group 1 L) (hirr : IsIrrOn L)
    (hS : Nat.card S = 2 ^ 14) {t : MulAut S} (ht : t ∈ L) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    6 ≤ disp t := by
  rcases u4RankDichotomySix_holds S 1 L le_rfl hL hirr with hnat | hbig
  · exfalso
    rcases finU4_natural_card hnat with h | h <;> rw [hS] at h <;>
      exact absurd h (by norm_num)
  · have h6 := hbig t ht ht1 ht2
    simpa [disp] using h6

end CFSG.LocalAnalysis.WeakClosure81
