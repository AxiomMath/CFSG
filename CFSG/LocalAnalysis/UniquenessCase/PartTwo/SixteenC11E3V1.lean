module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1S
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1Six
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1Ln
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Setup5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAlt6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAlt8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardAlt10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardSp6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s1611e3_normalizer_le_of_v1ne (hH1 : H1SpSixNatural) (hGap : S1611e3V1SixGap)
    {D : Data G} (h : S1611e3Std D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hcase : Case168_1 D ⊥ V hV L ∨ Case168_2Star D ⊥ V hV L ∨ Case168_5Star D ⊥ V hV L)
    (hv : v1Sub D.M ⊥ V hV L ≠ ⊥) : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have h125 : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hin : In10 D := h.in10 h125
  have h1610 : R16_10_2 D := h.r16_10_2 h125
  have hout : Out10 D ⊥ V hV := h.out10 hc
  have hs : s15 D.M ⊥ V hV L = 1 := s1611e3_s15_eq_one_of_starred h hc hcase
  rcases hcase with h1 | h2 | h5
  · exact s1611e3_v1_hard_case1 hGap h hc hs h1 hv
  · obtain ⟨hK, ⟨L₀, hdir, hfam⟩, hsig⟩ := h2
    have htop : wStar D.M ⊥ V hV L = ⊤ :=
      s15_Three_wStar_eq_top D h.h1217 hc.setting.hyp151 hV hc.ne_bot hs
    have key : ∀ {P : s16e_two_NatPred (vStar D.M ⊥ V hV L)}, s16e_two_Fam D ⊥ V L hV P →
        (∀ (H : Subgroup (MulAut (vStar D.M ⊥ V hV L))) (U Z : Subgroup (vStar D.M ⊥ V hV L)),
          P H U Z → ∃ D' : FFModel, S16C11V1ModelCover D' ∧ D'.Realizes H U Z) →
        normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := fun hF hP =>
      (hv (s16c11_v1_eq_bot_of_covers D hin h.h1217 hc hs hF hP)).elim
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
      · exact hodd (by decide) hn5 rfl
      · exact s16c11_v1_hard_alt_six D hin h.h1217 h1610 hc hs hout hsig hK hdir hL₀ hA hsum hv
      · exact key (s16e_two_fam_alt D hV hn5 hA hsum')
          (fun H U Z hP => ⟨FFModel.altDn 7, s16c11_v1_cover_alt_seven, hP⟩)
      · exact s16c11_v1_hard_alt_eight D hin h.h1217 h1610 hc hs
          (s1611e3_exists_noncyclic_three_of_sym hK hdir (by norm_num) hL₀) hout hsig hK hdir
          hL₀ hA hsum hv
      · exact hodd (by decide) hn5 rfl
      · exact s16c11_v1_hard_alt_ten D hin h.h1217 h1610 hc hs hout hsig hK hdir hL₀ hA hsum hv
      · exact hodd (by decide) hn5 rfl
    · have hsum' : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1) (lStar D.M ⊥ V hV L)
          (wStar D.M ⊥ V hV L) ⊥ 2 := by
        rw [htop]; exact hsum
      rcases (by omega : m = 3 ∨ m = 4 ∨ m = 5) with rfl | rfl | rfl
      · exact s1611e3_v1_hard_ln_three h hc hs hsig hK hdir hL₀ hLm hsum hv
      all_goals
        exact key (s16e_two_fam_ln D hV hm3 hLm hsum')
          (fun H U Z ⟨K, _, _, hK2, hR⟩ =>
            ⟨FFModel.nat (StatedSL _ K),
              s16c11_v1_cover_sl (by omega) (by simpa using hK2), hR⟩)
    · exact s16c11_v1_hard_sp_six hH1 D hin h.h1217 h1610 hc hs hout hsig hK hdir hL₀ hSp hsum hv
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
  · exact (hv (s16c11_v1_eq_bot_of_case5 D hin h.h1217 hc hs h5)).elim

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
