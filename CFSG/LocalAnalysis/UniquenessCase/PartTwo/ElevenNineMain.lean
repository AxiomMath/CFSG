module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

theorem r119_holds (D : Data G) (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h869 : F08.R869 D) (h111 : F11.R111 D)
    (h112 : F11.R112 D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) : F11.R119 D := by
  intro V₀ V hV hNorm X hX₀X hXM hlayer
  have h116 := c116_of_hyp11 D hSig h61 h63 h77 h111 h112 hV
  have h117 := c117_of_hyp11 D h869 hV
  have h118 := c118_of_hyp11 hThin hCyc D hV h116 h117
  obtain ⟨Y, hY, hMYX⟩ := exists_Y D hV h118 hX₀X hXM hlayer
  refine ⟨Y, hY, ?_⟩
  rintro ⟨Lbar, hL, hXbar⟩ hnt
  obtain ⟨hYX, hYperf, hO2E, -, hYC, hYbar⟩ := hY
  have hXn : D.M ≤ normalizer (X : Set G) := by
    refine le_normalizer_of_normal_barImage11 hX₀X hXM ?_
    rw [hXbar]
    exact normal_iSup_conj Lbar
  obtain ⟨K, hK, hYK⟩ := exists_calC_conjClosure_eq D hV (hYX.trans hXM) (hMYX hXn) hYperf hO2E
    hYC hL (hYbar.trans hXbar)
  obtain ⟨-, -, hV₀n, -⟩ := uc22p22q_hyp11_unpack D hV
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2
    (le_centralizer_of_not_thin D h869 hV₀n (card_le_four_or_eight_le D hV)
      (not_uniqueMax_of_eight_le D hV) hK hYK hnt)

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
