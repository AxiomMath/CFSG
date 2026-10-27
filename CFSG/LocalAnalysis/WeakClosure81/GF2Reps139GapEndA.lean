module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKEndF2Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem gapEndSp62_holds : GapEndSp62 := by
  intro W _ _ hW L hL hirr hcard
  have hrk : rk ↥(⊤ : Subgroup W) = 8 := by
    rw [rk, Subgroup.card_top, hcard, padicValNat.prime_pow]
  refine (Subgroup.eq_bot_iff_forall _).2 fun c hc => ?_
  rw [Subgroup.mem_centralizer_iff] at hc
  exact rSp6SpinCent_holds rSp6SpinUnique_holds W hW L hL hrk hirr c fun h hh => (hc h hh).symm

theorem gapEndL52_holds :
    GapEndL52 := by
  intro W _ _ hW L hSL hirr hcard
  exact s16kEndF2Rank10_holds W hW hcard L (fun B hB => hirr.2.2.2 B hB bot_le le_top)
    (Or.inl (s16k_isLn_of_isSLn (by norm_num) hSL))

theorem gapEndM22_holds :
    GapEndM22 := by
  intro W _ _ hW L hM hirr hcard
  exact s16kEndF2Rank10_holds W hW hcard L (fun B hB => hirr.2.2.2 B hB bot_le le_top) (Or.inr hM)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
