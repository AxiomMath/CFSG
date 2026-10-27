module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.AdapterThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.LocalAnalysis.RankThreeUC

theorem ascSixteenSixtyNine_of_thm1669
    (h : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), CFSG.Open.rankThreeUC G →
      ∀ S : Setup G, S.InMSigma → Thm1669 (dataOfSetup hS S)) :
    CFSG.Yardstones.Me2c15c2c995a.AscSixteenSixtyNine := by
  unfold CFSG.Yardstones.Me2c15c2c995a.AscSixteenSixtyNine
  intro G _ _ hS hUC S hMS V₀ V h125 hcard
  have h125' : Hyp125 (dataOfSetup hS S) V₀ V :=
    ⟨(hyp123_iff S.witness.maxLocal S.T V₀ V).1 h125.1, h125.2⟩
  exact (mBarGT3_iff S.M V₀ V).2 (h G hS hUC S hMS V₀ V h125' hcard)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
