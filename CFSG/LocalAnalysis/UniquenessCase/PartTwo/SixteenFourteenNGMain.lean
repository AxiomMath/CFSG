module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenGap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3ThirteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGRow2Core
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGRow3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGCase4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAEMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BetaMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10MBarFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s1614_no_min_not_gamma (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    (h1219loc : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1) (h153 : R15_3Small D)
    (h164 : R16_4 D) (h13b : R16_13_2 D) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV) {U : Subgroup G} (hU : Min1614 D V U)
    (hUΓ : U ∉ gammaEleven D.M V) : False := by
  classical
  have h1219 : D.sig = D.sig1 := h1219loc ⊥ V hc.setting.hyp16.hyp125
  have hS : Sect16 D ⊥ V L hV := ⟨hc.setting, hc.ne_bot, hc.conc⟩
  have hm1 : 1 < mBar D.M ⊥ V hV := r1613g_one_lt_mBar_of_four D hx h61 h127 h1217 h153 h4 hc
  have hge : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p (Mbar D.M ⊥ V hV) := fun p hp =>
    s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hc.setting.hyp16 hV h4 hp
  have hk2 : D.k ≤ 2 := s16c167_k_le_two D
  rcases h13b ⊥ V L hV hc with h2 | h4w | h3 | h8 | h9 | h10 | h11
  ·
    have hk1 : D.k = 1 := Data.k_eq_one_of_three_mem D hSg h1219
      (by rw [h2.2.2]; exact Set.mem_singleton 3)
    obtain ⟨J₀, J₁, -, -, -, -, h4J, -⟩ := s1614_row2_summand D h2
    have hJ : rk ↥J₀ ≤ rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) := rk_mono le_top
    rw [rk_top] at hJ
    exact s1614_false_of_row D h61 hV hc hU hUΓ (by omega) (by omega)
      (s1614_row2_hrow D hV hc h2 hk1)
  ·
    have hrk := s1614_row4_rk D hV h4w
    obtain ⟨p, hp, h4At⟩ := h4w
    have hk : D.k < mBar D.M ⊥ V hV := by
      rcases hp with rfl | rfl
      · have := Data.k_eq_one_of_three_mem D hSg h1219 h4At.2.2
        omega
      · have := s16c1610_two_lt_mBar_of_case4_seven D hx h61 h127 h4 hc (by norm_num : 1 < 3)
          h4At
        omega
    exact s1614_false_of_row D h61 hV hc hU hUΓ hk (by omega)
      (s1614_row4_hrow D hSg h1219 hV hc ⟨p, hp, h4At⟩ hge)
  ·
    have h3σ : (3 : ℕ) ∈ D.sig := by
      rw [h3.2.2]
      exact Set.mem_singleton 3
    have hk1 : D.k = 1 := Data.k_eq_one_of_three_mem D hSg h1219 h3σ
    have h6 : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 6 := h3.2.1
    rw [rk_top] at h6
    exact s1614_false_of_row D h61 hV hc hU hUΓ (by omega) (by omega)
      (s1614_row3_hrow D hV hc h3 hk1 (hge 3 h3σ))
  · exact r1613g_not_case168_8_of_four D hx h61 h127 h4 hS h8
  · exact s16ae_false_of_case168_9_of_r16_4 D hx h164 h4 hc h9
  · exact s16ae_false_of_case168_10_of_r16_4 D hx h164 h4 hc h10
  · exact s16c1610_false_of_case11_four D hx h61 h127 hc h4 h11

theorem s1614_gapFourteenBlock (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    (h1219loc : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1) (h153 : R15_3Small D)
    (h164 : R16_4 D) (h111 : W3Thm111 G) (h12 : R16_12 D) : S16GapFourteenBlock D := by
  have h13b : R16_13_2 D := r16_13_2_holds D hx h61 h111 hSg h12
    (r1613g_gapMGtOne_of_four D hx h61 h127 h1217 h153 h4)
    (s16GapInspBC_holds D hx h61 h127 h4 hSg h12) (s16GapInspA_holds D hx h61 h127 h4 h12)
    (s16GapAEmpty_of_four D hx h61 h127 h1217 h153 h164 h4)
    (s16GapBetaBound_holds D hSg h1219loc h61)
  intro V L hV hc U hU hUΓ
  exact (s1614_no_min_not_gamma D hx h4 hSg h61 h127 h1217 h1219loc h153 h164 h13b hV hc hU
    hUΓ).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
