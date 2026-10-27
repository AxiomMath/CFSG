module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RLstar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_38_rankGap_holds (D : Data G) (h119 : F11.R119 D) (h127 : R127 D) :
    R16_38_rankGap D := by
  intro _ _ _ _ _ _ _ V₀ V L hV hS m hm _ _ _ _ hq a E haE haM hEle hcomm hexp hcard
  obtain ⟨Lst, hLM, hLn, hLC, hbar⟩ := exists_Lstar_of_case1633 D h119 h127 hS hm
  have h125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  exact three_le_pRank_of_Lstar hMs hq hLM hLn hLC haE haM (by rw [hbar]; exact hEle) hcomm
    hexp hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
