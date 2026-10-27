module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114E3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20r
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4L52
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3URank
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114CoverE6
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251h
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PC
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.S15 (rkLin eP)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]


theorem uc22s2114_e3r4_four_le_pRank
    (hGA : GriessAllModelsStatement) (hN : uc22p20rNativeGriess) {M L : Subgroup G}
    (hL : L ∈ calC M) {t : StatedLieTag} {m f : ℕ} (hadm : StatedLieAdmissible t m 2 f)
    (hX : LieModel (BarInf L) t m 2 f) (hl : 4 ≤ PartTwo.S17.CS17LieRank t m)
    (hL52 : ¬ (t = .PSL ∧ f = 1 ∧ m ≤ 7)) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 4 ≤ CFSG.Open.pRank r L := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hM := LieModel.of_mulEquiv e hX
  have hq := hL.2.2
  have hodd := uc22p20p_odd_center_bar2 ↥L
  have hf : 1 ≤ f := hadm.2.1
  have hT := uc22p20x_lieOddRankChev hGA
  have h3 : (3 : ℕ) ≠ 2 := by norm_num
  have hbar : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) →
      ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 4 ≤ CFSG.Open.pRank r L := fun h =>
    ⟨3, Nat.prime_three, h3, by rwa [← pRank_bar2_eq_of_odd Nat.prime_three h3]⟩
  cases t with
  | PSL =>
    have hm : 5 ≤ m := by change 4 ≤ m - 1 at hl; omega
    obtain rfl | hf2 : f = 1 ∨ 2 ≤ f := by omega
    · have hm8 : 8 ≤ m := by
        by_contra h
        exact hL52 ⟨rfl, rfl, by omega⟩
      refine hbar ?_
      rw [uc22s2114_pRank_psl_of_five_le hT hq (hM.statedClassicalModel (by decide)) hm
        Nat.prime_three h3,
        uc22p20v_rkLin_true_two
        (by rw [uc22p20v_eP_three, if_neg (by decide)] : eP (2 ^ 1) 3 = 2)]
      omega
    · obtain ⟨r, hr, hrf, hr5⟩ := uc22p20o_prime_sub_one_ne_five hf2
      have hr2 : r ≠ 2 := by
        rintro rfl
        have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        omega
      refine ⟨r, hr, hr2, ?_⟩
      rw [← pRank_bar2_eq_of_odd hr hr2,
        uc22s2114_pRank_psl_of_five_le hT hq (hM.statedClassicalModel (by decide)) hm hr hr2]
      exact uc22p20v_four_le_rkLin_true_one hr (uc22p20v_eP_of_dvd hrf) hm fun _ => hr5
  | PSU =>
    have hm : 8 ≤ m := by change 4 ≤ m / 2 at hl; omega
    have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    obtain ⟨r, hr, hrf⟩ := Nat.exists_prime_and_dvd (n := 2 ^ f + 1) (by omega)
    have hr2 : r ≠ 2 := by
      rintro rfl
      have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      omega
    exact ⟨r, hr, hr2, uc22s2114r3u_four_le_pRank hGA hL (by omega) hX hr hr2
      (fun h => absurd h (by omega)) hrf⟩
  | PSp =>
    refine hbar ?_
    rw [uc22p20w_pRank_psp hT hq (hM.statedClassicalModel (by decide)) Nat.prime_three h3,
      uc22p20v_rkSp_of_eS (uc22p20v_eS_three f)]
    exact hl
  | POmegaOdd => exact (hadm.2.2.2 rfl).elim
  | POmegaPlus =>
    refine hbar ?_
    rw [uc22p20w_pRank_pomegaPlus hT hq (hM.statedClassicalModel (by decide)) Nat.prime_three h3]
    exact uc22p20v_rkOmPlus_ge hadm.2.2 (uc22p20v_eS_three f) (uc22p20v_eP_three_cases f)
  | POmegaMinus =>
    have hm : 5 ≤ m := by change 4 ≤ m - 1 at hl; omega
    refine hbar ?_
    rw [uc22p20w_pRank_pomegaMinus hT hq (hM.statedClassicalModel (by decide)) Nat.prime_three
      h3]
    exact le_trans (by omega) (uc22p20v_rkOmMinus_ge (l := m) (uc22p20v_eS_three f))
  | F4 =>
    exact hbar (uc22p20w_four_le_pRank_three_exc (uc22p20v_center_f4 hN hq hodd hM) (by simp) hf
      hM)
  | E7 =>
    exact hbar (uc22p20w_four_le_pRank_three_exc (uc22p20v_center_e7 hN hq hodd hf hM) (by simp)
      hf hM)
  | E8 =>
    exact hbar (uc22p20w_four_le_pRank_three_exc (uc22p20v_center_e8 hN hq hodd hM) (by simp) hf
      hM)
  | E6 =>
    refine hbar ?_
    by_cases h3f : 3 ∣ 2 ^ f - 1
    · exact four_le_pRank_three_of_cover_E6_two hM h3f
    · have hZd : Nat.card (center (Bar2 L)) ∣ Nat.gcd 3 (2 ^ f - 1) * 1 :=
        uc22p20v_card_center_dvd hN hq hodd hM
      rw [mul_one, ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3f).gcd_eq_one,
        Nat.dvd_one] at hZd
      exact uc22p20w_four_le_pRank_three_exc (Subgroup.card_eq_one.mp hZd) (by simp) hf hM
  | twistedE6 =>
    refine hbar ?_
    by_cases h3f : 3 ∣ 2 ^ f + 1
    · exact four_le_pRank_three_of_cover_twistedE6_two hM h3f
    · have hZd : Nat.card (center (Bar2 L)) ∣ Nat.gcd 3 (2 ^ f + 1) * 1 :=
        uc22p20v_card_center_dvd hN hq hodd hM
      rw [mul_one, ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3f).gcd_eq_one,
        Nat.dvd_one] at hZd
      exact uc22p20w_four_le_pRank_three_exc (Subgroup.card_eq_one.mp hZd) (by simp) hf hM
  | _ => simp [PartTwo.S17.CS17LieRank] at hl

theorem s21_14R4_of_s21_14R4T
    (hGA : GriessAllModelsStatement) (hN : uc22p20rNativeGriess) {D : Data G}
    {Ch : Choice2011 G} (hM3 : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q D.M ≤ 3)
    (h82 : F08.R82 D) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h3 : S21_3 D Ch)
    (h5 : S21_5 D Ch) (hR4T : S21_14R4T D Ch) : S21_14R4 D Ch := by
  rintro hH c L hL hX hpow ⟨l, f, hl4, t, m, hadm, hmod, rfl⟩
  by_cases hL52 : t = .PSL ∧ f = 1 ∧ m ≤ 7
  · obtain ⟨rfl, rfl, hm7⟩ := hL52
    have hm : 5 ≤ m := by change 4 ≤ m - 1 at hl4; omega
    have h3L : CFSG.Open.pRank 3 L = m / 2 := by
      obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
      rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num),
        uc22s2114_pRank_psl_of_five_le (uc22p20x_lieOddRankChev hGA) hL.2.2
          ((LieModel.of_mulEquiv e hmod).statedClassicalModel (by decide)) hm Nat.prime_three
          (by norm_num),
        uc22p20v_rkLin_true_two
          (by rw [uc22p20v_eP_three, if_neg (by decide)] : eP (2 ^ 1) 3 = 2)]
    have hBL := uc22s2114_B0_le_normalizer h5 hH c hL
    have hfaith := uc22s2114_faithful h3 hH c hL fun hthin => by
      have := hthin 3 Nat.prime_three (by norm_num)
      omega
    have hk1 : D.k = 1 → Odd c.n ∧ c.B0 ≤ normalizer (D.T : Set G) := fun hk => by
      have hodd := u4p_odd_n D Ch hH c (uc22p2251h_isStronglyPEmbedded D hk)
      exact ⟨hodd, u4x_B0_le_normalizer c hodd⟩
    obtain rfl | h67 : m = 5 ∨ (m = 6 ∨ m = 7) := by omega
    · by_cases h4 : 4 ∣ c.n
      · exact (uc22s2114_false_of_isL5_two c hL hmod h4 hBL hfaith).elim
      · exact hR4T hH c L hL hX hpow (Or.inl ⟨hmod, h4⟩) (hn3 hH c) hBL hfaith hk1
    · have hk : D.k = 1 := by
        have h := h82 L ⟨hL.1, hL.2.1, by omega, Or.inl (PartTwo.s15_Three_qs_of_open hL.2.2)⟩
        unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
        rw [if_pos h]
      refine hR4T hH c L hL hX hpow (Or.inr ⟨?_, hk⟩) (hn3 hH c) hBL hfaith hk1
      rcases h67 with rfl | rfl
      · exact Or.inl hmod
      · exact Or.inr hmod
  · obtain ⟨r, hr, hr2, h4⟩ := uc22s2114_e3r4_four_le_pRank hGA hN hL hadm hmod hl4 hL52
    have := CFSG.SectionRank.pRank_mono hr.one_lt hL.1.le
    have := hM3 r hr hr2
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
