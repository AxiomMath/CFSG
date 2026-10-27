module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22th
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofSub

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KBridge

theorem kThinSimple_of_thinList13 (h : PartTwo.ThinList13) : KThinSimple := by
  intro Q _ _ hK hs hna hcyc
  haveI := hs
  have hq : CFSG.Open.IsQuasisimple Q := CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).1
  have hr : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r Q ≤ 1 := fun r hr hr2 =>
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_sylow_cyclic hr
      (hcyc r hr hr2)
  obtain ⟨-, hL | ⟨p, hp, hp2, hL⟩ | hSz | hJ⟩ := h Q hK hq
    (CFSG.RankThree.PartTwo.Sec14.Main148.pCore_two_eq_bot_of_isSimpleGroup hs hna) hr
  · exact Or.inl hL
  · obtain ⟨-, -, -, -, h3⟩ := CFSG.Blueprint.LieModel.admissible hL
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact h3 rfl
    exact Or.inr (Or.inr (Or.inl ⟨p, hp, hp.five_le_of_ne_two_of_ne_three hp2 hp3, hL⟩))
  · exact Or.inr (Or.inl hSz)
  · exact Or.inr (Or.inr (Or.inr hJ))

theorem kThinSimple_holds :
    KThinSimple :=
  kThinSimple_of_thinList13 PartTwo.thinList13_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22.KBridge
