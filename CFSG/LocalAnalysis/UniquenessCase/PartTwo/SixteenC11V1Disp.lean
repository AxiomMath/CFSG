module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Setup5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAlt6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAlt8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAlt10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardSp6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Small
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightLemE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Dispatcher


theorem s16c11_normalizer_le_of_v1 (hH1 : H1SpSixNatural) (D : Data G) (hin : In10 D)
    (h1217 : R1217 D) (h1610 : R16_10_2 D) (h4 : 3 < CFSG.Open.evenRank G) (h164 : R16_4 D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hout : Out10 D ⊥ V hV)
    (h25 : Case168_2Star D ⊥ V hV L ∨ Case168_5Star D ⊥ V hV L)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hs : s15 D.M ⊥ V hV L = 1 :=
    s16f_s15_eq_one_of_four D hin.hx h4 hin.h61 hin.h127 h1217 h164 hV hc.setting hc.ne_bot
      hc.conc
  rcases h25 with h2 | h5
  · obtain ⟨hK, ⟨L₀, hdir, hfam⟩, hsig⟩ := h2
    have htop : wStar D.M ⊥ V hV L = ⊤ :=
      s15_Three_wStar_eq_top D h1217 hc.setting.hyp151 hV hc.ne_bot hs
    have hm : 3 ≤ CFSG.Open.pRank 3 (Mbar D.M ⊥ V hV) :=
      s16c1610_three_le_pRank_mBar_of_four D hin.hx hin.h61 hin.h127 hc.setting.hyp16 hV h4
        (by rw [hsig]; exact Set.mem_singleton 3)
    have hsmall : ¬ (IsSym ↥L₀ 5 ∨ IsLn ↥L₀ 3 1) := fun h =>
      absurd hm (not_le.2 (lt_of_le_of_lt (s16c11_pRank_three_le_two_of_small hdir hK h)
        (by norm_num)))
    have key : ∀ {P : s16e_two_NatPred (vStar D.M ⊥ V hV L)}, s16e_two_Fam D ⊥ V L hV P →
        (∀ (H : Subgroup (MulAut (vStar D.M ⊥ V hV L))) (U Z : Subgroup (vStar D.M ⊥ V hV L)),
          P H U Z → ∃ D' : FFModel, S16C11V1ModelCover D' ∧ D'.Realizes H U Z) →
        normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := fun hF hP =>
      (hV1 (s16c11_v1_eq_bot_of_covers D hin h1217 hc hs hF hP)).elim
    rcases hfam with ⟨n, hn5, hn11, hL₀, hA, hsum⟩ | ⟨m, hm3, hm5, hL₀, hLm, hsum⟩ |
        ⟨hL₀, hSp, hsum⟩ | ⟨hL₀, hO, hsum⟩ | ⟨hL₀, hO, hsum⟩
    · have hsum' : SumOfNat (fun H U Z => AlternatingNatural H U Z n) (lStar D.M ⊥ V hV L)
          (wStar D.M ⊥ V hV L) ⊥ 2 := by
        rw [htop]; exact hsum
      have hodd : ∀ {k : ℕ}, Odd k → 5 ≤ k → n = k →
          normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := fun hk hk5 hnk => by
        subst hnk
        exact key (s16e_two_fam_alt D hV hn5 hA hsum')
          (fun H U Z hP => ⟨FFModel.altDn n, s16c11_v1_cover_alt_odd hk hk5, hP⟩)
      rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hsmall (Or.inl hL₀)).elim
      · exact s16c11_v1_hard_alt_six D hin h1217 h1610 hc hs hout hsig hK hdir hL₀ hA hsum
          hV1
      · exact key (s16e_two_fam_alt D hV hn5 hA hsum')
          (fun H U Z hP => ⟨FFModel.altDn 7, s16c11_v1_cover_alt_seven, hP⟩)
      · exact s16c11_v1_hard_alt_eight D hin h1217 h1610 hc hs
          (s16c11_v1_alt_eight_three D hin h4 hc hsig) hout hsig hK hdir hL₀ hA hsum
          hV1
      · exact hodd (by decide) hn5 rfl
      · exact s16c11_v1_hard_alt_ten D hin h1217 h1610 hc hs hout hsig hK hdir hL₀ hA hsum
          hV1
      · exact hodd (by decide) hn5 rfl
    · have hsum' : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1) (lStar D.M ⊥ V hV L)
          (wStar D.M ⊥ V hV L) ⊥ 2 := by
        rw [htop]; exact hsum
      rcases (by omega : m = 3 ∨ m = 4 ∨ m = 5) with rfl | rfl | rfl
      · exact (hsmall (Or.inr hL₀)).elim
      all_goals
        exact key (s16e_two_fam_ln D hV hm3 hLm hsum')
          (fun H U Z ⟨K, _, _, hK2, hR⟩ =>
            ⟨FFModel.nat (StatedSL _ K),
              s16c11_v1_cover_sl (by omega) (by simpa using hK2), hR⟩)
    · exact s16c11_v1_hard_sp_six hH1 D hin h1217 h1610 hc hs hout hsig hK hdir hL₀ hSp hsum
        hV1
    · have hsum' : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1) (lStar D.M ⊥ V hV L)
          (wStar D.M ⊥ V hV L) ⊥ 2 := by
        rw [htop]; exact hsum
      exact key (s16e_two_fam_om D hV (Or.inl rfl) hO hsum')
        (fun H U Z ⟨_, K, _, _, b, c, hK2, hirr, hR⟩ =>
          ⟨FFModel.nat (StatedOmega (StatedQuadMinus (6 / 2) K b c)),
            (show (6 : ℕ) / 2 = 3 from rfl) ▸
              s16c11_v1_cover_omegaMinus_six (K := K) (by simpa using hK2) hirr, hR⟩)
    · have hsum' : SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1) (lStar D.M ⊥ V hV L)
          (wStar D.M ⊥ V hV L) ⊥ 2 := by
        rw [htop]; exact hsum
      exact key (s16e_two_fam_om D hV (Or.inr rfl) hO hsum')
        (fun H U Z ⟨_, K, _, _, b, c, hK2, hirr, hR⟩ =>
          ⟨FFModel.nat (StatedOmega (StatedQuadMinus (8 / 2) K b c)),
            (show (8 : ℕ) / 2 = 4 from rfl) ▸
              s16c11_v1_cover_omegaMinus_eight (K := K) (by simpa using hK2) hirr, hR⟩)
  · exact (hV1 (s16c11_v1_eq_bot_of_case5 D hin h1217 hc hs h5)).elim

end Dispatcher

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
