module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3ThirteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Twelve
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGRow2Core
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGRow3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGCase4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Row3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Row4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Row8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Row9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Row10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Row11
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3Out4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenSeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s1614e3_gapFourteenBlock (D : Data G) (hx : DataExt D) (hSg : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D) (h1214 : F12.R1214 D)
    (h1219 : D.sig = D.sig1) (hM : S16GapMGtOne D) (h13b : R16_13_2 D) :
    S16GapFourteenBlock D := by
  intro V L hV hc U hU hUΓ
  have hm1 : 1 < mBar D.M ⊥ V hV := hM V L hV hc
  have hk2 : D.k ≤ 2 := s16c167_k_le_two D
  rcases h13b ⊥ V L hV hc with h2 | h4w | h3 | h8 | h9 | h10 | h11
  ·
    exfalso
    have hk1 : D.k = 1 := Data.k_eq_one_of_three_mem D hSg h1219
      (by rw [h2.2.2]; exact Set.mem_singleton 3)
    obtain ⟨J₀, J₁, -, -, -, -, h4J, -⟩ := s1614_row2_summand D h2
    have hJ : rk ↥J₀ ≤ rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) := rk_mono le_top
    rw [rk_top] at hJ
    exact s1614_false_of_row D h61 hV hc hU hUΓ (by omega) (by omega)
      (s1614_row2_hrow D hV hc h2 hk1)
  ·
    exfalso
    have hrk := s1614_row4_rk D hV h4w
    obtain ⟨p, hp, h4At⟩ := h4w
    have hp0 := hp
    have hpp : p.Prime := by rcases hp0 with rfl | rfl <;> norm_num
    have hge := s1614e3_three_le_pRank_of_case4At D hc hpp h4At
    have hk : D.k < mBar D.M ⊥ V hV := by
      rcases hp with rfl | rfl
      · have := Data.k_eq_one_of_three_mem D hSg h1219 h4At.2.2
        omega
      · have := s16t_two_lt_mBar_of_case4_seven D hc (by norm_num : 1 < 3) h4At
        omega
    exact s1614_false_of_row D h61 hV hc hU hUΓ hk (by omega)
      (s1614e3_row4_hrow D hSg h1219 hV hc hp0 h4At hge)
  ·
    have h3σ : (3 : ℕ) ∈ D.sig := by
      rw [h3.2.2]
      exact Set.mem_singleton 3
    have hk1 : D.k = 1 := Data.k_eq_one_of_three_mem D hSg h1219 h3σ
    by_cases hpr : 3 ≤ CFSG.Open.pRank 3 (Mbar D.M ⊥ V hV)
    · exfalso
      have h6 : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 6 := h3.2.1
      rw [rk_top] at h6
      exact s1614_false_of_row D h61 hV hc hU hUΓ (by omega) (by omega)
        (s1614_row3_hrow D hV hc h3 hk1 hpr)
    · exact Or.inr (s1614e3_row3_close D hx hSg h1219 h61 h127 hV hc h3 hm1 (not_le.1 hpr) hU hUΓ)
  · exact (s1614e3_row8_false D hx hSg h61 h127 h1214 h1219 hV hc h8 hm1 hU hUΓ).elim
  · exact (s1614e3_row9_false D h61 h1217 hV hc h9 hU hUΓ).elim
  ·
    exfalso
    obtain ⟨p, hp, h10At⟩ := h10
    have hrk := s1614e3_row10_rk D h1217 hV hc hp h10At
    have hk : D.k < mBar D.M ⊥ V hV := by
      rcases hp with rfl | rfl
      · have := Data.k_eq_one_of_three_mem D hSg h1219
          (by rw [h10At.2.2.2.1]; exact Set.mem_singleton 3)
        omega
      · have := s16t_two_lt_mBar_of_case168_10_seven D h1217 hc h10At
        omega
    exact s1614_false_of_row D h61 hV hc hU hUΓ hk (by omega)
      (s1614e3_row10_hrow D hSg h1219 h1217 hV hc hp h10At)
  ·
    exact Or.inr (s1614e3_row11_close D hx h61 h127 h1217 hV hc h11 hU hUΓ)

theorem s1614e3_gapFourteenBlock_of_inputs (D : Data G) (hx : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    (h1214 : F12.R1214 D) (h1219 : D.sig = D.sig1) (h10 : R16_10_1 D) (h11 : R16_11 D)
    (h111 : W3Thm111 G) (hM : S16GapMGtOne D) (hBC : S16GapInspBC D) (hA : S16GapInspA D)
    (hAE : S16GapAEmpty D) (hβ : S16GapBetaBound D) : S16GapFourteenBlock D :=
  s1614e3_gapFourteenBlock D hx hSg h61 h127 h1217 h1214 h1219 hM
    (r16_13_2_holds D hx h61 h111 hSg (sixteen_seven2_twelve D h10 h11) hM hBC hA hAE hβ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
