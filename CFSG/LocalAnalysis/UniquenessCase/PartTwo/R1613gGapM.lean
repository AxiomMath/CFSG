module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gMParam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gCase153
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gCase168
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapM

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r1613g_gapMGtOne_of_four (D : Data G) (hext : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1217 : R1217 D) (h153 : R15_3Small D)
    (h4 : 3 < CFSG.Open.evenRank G) : S16GapMGtOne D := by
  intro V L hV hc
  by_contra hlt
  have hS : Sect16 D ⊥ V L hV := ⟨hc.setting, hc.ne_bot, hc.conc⟩
  have hMne : Mbar D.M ⊥ V hV ≠ ⊥ := by
    intro hbot
    apply hc.ne_bot
    exact le_bot_iff.mp
      ((barSub_mono ⊥ V hV hc.setting.hyp151.le).trans (le_of_eq hbot))
  have hne : mBar D.M ⊥ V hV ≠ 0 :=
    r1613g_mParam_ne_zero (s15_Infra_vtil_sq_eq_one ⊥ V hV) hMne
  have hm1 : mBar D.M ⊥ V hV = 1 := by omega
  rcases sixteen_one D h1217 h153 hc.setting.hyp151 hc.setting.hyp16.small hV hc.ne_bot hm1 with
    h1 | h2 | h3
  · have h3sig : 3 ∈ D.sig := by rw [h1.2.2.1]; exact Set.mem_singleton 3
    have h4' := hext.four_le h4 3 h3sig
    have h3rk := h1.2.2.2.1
    omega
  · obtain ⟨K₀, p, -, -, -, hsig, hrk, -⟩ := h2
    have hp : p ∈ D.sig := by rw [hsig]; exact Set.mem_singleton p
    have h4' := hext.four_le h4 p hp
    omega
  · obtain ⟨hcard, hrk⟩ := r1613g_case153_3_summary D hc.conc h3
    have h8 := r1613g_case168_eight_of_card_three D hcard hrk hc.concl168
    exact r1613g_not_case168_8_of_four D hext h61 h127 h4 hS h8

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
