module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gCase153
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3Case2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_row153_3 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) (h : Case153_3 D V₀ V hV L) :
    False := by
  obtain ⟨-, hrk⟩ := r1613g_case153_3_summary D c.conc h
  rw [wTil_eq_top_of_case163_2 c.conc hs] at hrk
  exact c.false_of_rk_le_two hrk

theorem s168e3_s2_153_2 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 2)
    (hγ : gamma15 D.M V₀ V hV L ≤ 3) (h : Case153_2 D V₀ V hV L) : Case167_2 D V₀ V hV L := by
  obtain ⟨K₀, p, hKL, hcases, hdir, hsig, -, hcnt, -⟩ := h
  have hcnt1 : (conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard ≤ 1 := by
    rw [hs] at hcnt
    omega
  have hpos : 0 < (conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2
      ⟨barSub V₀ V hV K₀, 1, Subgroup.one_mem _, by ext x; simp⟩
  have hr : (conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard = 1 := by
    omega
  rcases hcases with ⟨-, -, hnat⟩ | ⟨hp7, hK, hnat⟩
  · have h151 : Hyp151 D V₀ V L := c.setting.hyp151
    have hLK : lBar V₀ V hV L = barSub V₀ V hV K₀ := s15_Three_eq_of_ncard_conjSet hdir hr
    have hstar : lStar D.M V₀ V hV L = barSub (v1Sub D.M V₀ V hV L) V hV K₀ :=
      (s15_Three_barSub_star_iff D c.std.h1217 h151 h151.le (hKL.trans h151.le)).1 hLK
    have hW : commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀) = wStar D.M V₀ V hV L := by
      rw [← hstar]
      exact s15_Three_commSub_top_lStar h151 hV
    have hcard : Nat.card ↥(wStar D.M V₀ V hV L) = 2 ^ (5 - 1) := by
      rw [← hW]
      exact s16c1610_card_alternatingNatural_odd (by decide) hnat
    have hrk : rk ↥(wStar D.M V₀ V hV L) = 4 := by
      have h4 := s16c1610_rk_of_card_two_pow hcard
      omega
    have hg4 : gamma15 D.M V₀ V hV L = 4 := hrk
    omega
  · rw [hp7] at hsig
    exact s16t_case167_2_of_conj_one D c.std.h1217 c.setting.hyp151 hV hKL hK hnat hdir hr hs hsig

theorem s168e3_s2_153_3 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 2) (h : Case153_3 D V₀ V hV L) :
    Case167_3 D V₀ V hV L := by
  obtain ⟨hcard, -⟩ := r1613g_case153_3_summary D c.conc h
  obtain ⟨⟨K₀, -, hcyc, hdir, hnat⟩, -⟩ := h
  have hK3 : Nat.card ↥(barSub V₀ V hV K₀) = 3 := hcyc.2
  have hKrk : rk ↥(commSub ⊤ (barSub V₀ V hV K₀)) = 2 :=
    s16c1610_rk_of_card_two_pow (s16c1610_card_alternatingNatural_odd (by decide) hnat)
  have hc1 := r1613g_card_directProd_of_conj hdir hK3
  have hpow : 3 ^ (conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard = 3 ^ 1 := by
    rw [← hc1, hcard]
    norm_num
  have hc1' : (conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard = 1 :=
    Nat.pow_right_injective (by norm_num) hpow
  have hLK : lBar V₀ V hV L = barSub V₀ V hV K₀ := s15_Three_eq_of_ncard_conjSet hdir hc1'
  have hrk : rk ↥(wTil V₀ V hV L) = 2 := by
    change rk ↥(commSub ⊤ (lBar V₀ V hV L)) = 2
    rw [hLK]
    exact hKrk
  have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by
    rw [hcard]
    decide
  have hV1 : v1Sub D.M V₀ V hV L = V₀ := s16e_v1Sub_eq_of_odd D hV hodd
  obtain ⟨g, hg⟩ := s16e_twoConj D c.std.h1217 hV c.setting c.ne hV1 hs
  have htop : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 4 := by
    have h2 := s16e_rk_top_eq_two_mul hg
    have hrk' : rk ↥(commSub ⊤ (lBar V₀ V hV L)) = 2 := hrk
    rw [h2, hrk']
  have hsig : D.sig = {3} := by
    have hmem : ∀ p ∈ D.sig, p = 3 := by
      intro p hp
      by_contra hp3
      have hpprime : p.Prime := (D.sig_prime p hp).1
      have hp2 : p ≠ 2 := (D.sig_prime p hp).2
      have hp5 : 5 ≤ p := by
        by_contra h5
        have hlt5 : p < 5 := not_le.1 h5
        have hp2le : 2 ≤ p := hpprime.two_le
        interval_cases p
        · exact hp2 rfl
        · exact hp3 rfl
        · norm_num at hpprime
      have hlt := s168e3_pRank_lt_two_of_rk_le_four (s15_Infra_vtil_sq_eq_one V₀ V hV)
        (d := rk ↥(⊤ : Subgroup (Vtil V₀ V hV))) (by omega)
        (s16e_card_eq_two_pow_rk_top (s15_Infra_vtil_sq_eq_one V₀ V hV)) hpprime hp5
        (Mbar D.M V₀ V hV)
      have h2 := c.two_le_pRank_mbar hp
      omega
    obtain ⟨p, hp⟩ := c.std.hx.sig_nonempty
    exact Set.eq_singleton_iff_unique_mem.2 ⟨hmem p hp ▸ hp, hmem⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨⟨isCyclic_of_prime_card hcard, hcard⟩, hrk, hs, hsig⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
