module

public import CFSG.LocalAnalysis.StandardType.GGResTwoSettledDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem ggTwoCensus_label_L_of_A {p l n : ℕ} (hl1 : 1 ≤ l) (himp : l = 1 → 2 ≤ n)
    (hs : LargeEvenSplit p ⟨.A, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.A, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.A, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.A, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.A, l, n⟩ := by
  simp [LargeEvenSplit, LargeEvenUntwisted] at hs
  rcases hs with hq | ⟨hn, hp3⟩
  · have hSL : ggTwoSettledLabelL p (⟨.A, l, n⟩ : LargeEvenLabel) := Or.inr (Or.inl ⟨rfl, hq⟩)
    exact Or.inr (Or.inl hSL)
  · subst hn
    subst hp3
    have hl2 : 2 ≤ l := by
      by_contra h
      have h1 : l = 1 := by omega
      exact absurd (himp h1) (by omega)
    by_cases hl4 : l ≤ 4
    · have hsmall : ggThreeSmallLabel 3 (⟨.A, l, 1⟩ : LargeEvenLabel) := by
        refine Or.inr (Or.inr (Or.inl ?_))
        exact ⟨rfl, rfl, Or.inl ⟨rfl, hl4⟩⟩
      exact Or.inr (Or.inr (Or.inl hsmall))
    · have hSL : ggTwoSettledLabelL 3 (⟨.A, l, 1⟩ : LargeEvenLabel) := by
        apply Or.inr
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
        exact ⟨rfl, rfl, rfl, by show 5 ≤ l; omega⟩
      exact Or.inr (Or.inl hSL)

private theorem ggTwoCensus_label_L_of_twA {p l n : ℕ} (hl2 : 2 ≤ l) (himp : l = 2 → 2 ≤ n)
    (hs : LargeEvenSplit p ⟨.twA, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.twA, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.twA, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.twA, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.twA, l, n⟩ := by
  simp [LargeEvenSplit, LargeEvenUntwisted] at hs
  rcases hs with hqplus | ⟨hn, hp3⟩
  · by_cases hl2' : l = 2
    · subst hl2'
      have hsmall : ggThreeSmallLabel p (⟨.twA, 2, n⟩ : LargeEvenLabel) := by
        simp [ggThreeSmallLabel, GGRootGenSmallRankLabel]
      exact Or.inr (Or.inr (Or.inl hsmall))
    · have hl3 : 3 ≤ l := by omega
      have hSL : ggTwoSettledLabelL p (⟨.twA, l, n⟩ : LargeEvenLabel) := by
        apply Or.inr
        refine Or.inr (Or.inl ?_)
        exact ⟨Or.inl ⟨rfl, hl3⟩, hqplus⟩
      exact Or.inr (Or.inl hSL)
  · subst hn
    subst hp3
    have hqplus : (3 : ℕ) ∣ 2 ^ 1 + 1 := by norm_num
    have hl3 : 3 ≤ l := by
      by_contra h
      have h2 : l = 2 := by omega
      exact absurd (himp h2) (by omega)
    have hSL : ggTwoSettledLabelL 3 (⟨.twA, l, 1⟩ : LargeEvenLabel) := by
      apply Or.inr
      refine Or.inr (Or.inl ?_)
      exact ⟨Or.inl ⟨rfl, hl3⟩, hqplus⟩
    exact Or.inr (Or.inl hSL)

private theorem ggTwoCensus_label_L_of_B_or_C {p l n : ℕ} {t : LargeEvenLieTag}
    (htag : t = .B ∨ t = .C) (hl2 : 2 ≤ l)
    (hs : p ∣ 2 ^ n - 1 ∨ n = 1 ∧ p = 3) :
    ggTwoSettledEitherLabelL p ⟨t, l, n⟩ ∨ ggTwoSettledLabelL p ⟨t, l, n⟩ ∨
      ggThreeSmallLabel p ⟨t, l, n⟩ ∨ ggTwoResidualLabelL p ⟨t, l, n⟩ := by
  by_cases hl2' : l = 2
  · subst hl2'
    have hsmall : ggThreeSmallLabel p (⟨t, 2, n⟩ : LargeEvenLabel) :=
      Or.inl (Or.inr (Or.inl ⟨htag, rfl⟩))
    exact Or.inr (Or.inr (Or.inl hsmall))
  · have hl3 : 3 ≤ l := by omega
    rcases hs with hq | ⟨hn, hp3⟩
    · by_cases hl5 : l ≤ 5
      · have hres : ggTwoResidualLabelL p (⟨t, l, n⟩ : LargeEvenLabel) := by
          refine Or.inl ?_
          exact ⟨Or.inl ⟨htag, hl5⟩, hl3, hq⟩
        exact Or.inr (Or.inr (Or.inr hres))
      · have hHigh : ggTwoSettledLabelL p (⟨t, l, n⟩ : LargeEvenLabel) :=
          Or.inl ⟨htag, by show 6 ≤ l; omega, hq⟩
        exact Or.inr (Or.inl hHigh)
    · subst hn
      subst hp3
      by_cases hl3' : l = 3
      · subst hl3'
        have hSL : ggTwoSettledLabelL 3 (⟨t, 3, 1⟩ : LargeEvenLabel) := by
          apply Or.inr
          refine Or.inr (Or.inr (Or.inl ?_))
          exact ⟨rfl, htag, rfl, rfl⟩
        exact Or.inr (Or.inl hSL)
      · by_cases hl4 : l = 4
        · subst hl4
          have hSL : ggTwoSettledLabelL 3 (⟨t, 4, 1⟩ : LargeEvenLabel) := by
            apply Or.inr
            refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
            exact ⟨rfl, htag, rfl, rfl⟩
          exact Or.inr (Or.inl hSL)
        · have hl5 : 5 ≤ l := by omega
          have hSE : ggTwoSettledEitherLabelL 3 (⟨t, l, 1⟩ : LargeEvenLabel) := by
            refine Or.inl ?_
            exact ⟨rfl, htag, rfl, hl5⟩
          exact Or.inl hSE

private theorem ggTwoCensus_label_L_of_B {p l n : ℕ} (hl2 : 2 ≤ l)
    (hs : LargeEvenSplit p ⟨.B, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.B, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.B, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.B, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.B, l, n⟩ := by
  have hs' : p ∣ 2 ^ n - 1 ∨ n = 1 ∧ p = 3 := by
    simpa [LargeEvenSplit, LargeEvenUntwisted] using hs
  exact ggTwoCensus_label_L_of_B_or_C (Or.inl rfl) hl2 hs'

private theorem ggTwoCensus_label_L_of_C {p l n : ℕ} (hl2 : 2 ≤ l)
    (hs : LargeEvenSplit p ⟨.C, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.C, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.C, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.C, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.C, l, n⟩ := by
  have hs' : p ∣ 2 ^ n - 1 ∨ n = 1 ∧ p = 3 := by
    simpa [LargeEvenSplit, LargeEvenUntwisted] using hs
  exact ggTwoCensus_label_L_of_B_or_C (Or.inr rfl) hl2 hs'

private theorem ggTwoCensus_label_L_of_D {p l n : ℕ} (hl3 : 3 ≤ l)
    (hs : LargeEvenSplit p ⟨.D, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.D, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.D, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.D, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.D, l, n⟩ := by
  simp [LargeEvenSplit, LargeEvenUntwisted] at hs
  rcases hs with hq | ⟨hn, hp3⟩
  · have hres : ggTwoResidualLabelL p (⟨.D, l, n⟩ : LargeEvenLabel) := by
      refine Or.inl ?_
      exact ⟨Or.inr (Or.inl rfl), hl3, hq⟩
    exact Or.inr (Or.inr (Or.inr hres))
  · subst hn
    subst hp3
    by_cases hl3' : l = 3
    · subst hl3'
      have hsmall : ggThreeSmallLabel 3 (⟨.D, 3, 1⟩ : LargeEvenLabel) := by
        refine Or.inr (Or.inr (Or.inl ?_))
        exact ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
      exact Or.inr (Or.inr (Or.inl hsmall))
    · have hl4 : 4 ≤ l := by omega
      have hSL : ggTwoSettledLabelL 3 (⟨.D, l, 1⟩ : LargeEvenLabel) := by
        apply Or.inr
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        exact ⟨rfl, Or.inl rfl, rfl, hl4⟩
      exact Or.inr (Or.inl hSL)

private theorem ggTwoCensus_label_L_of_twD_dvd_pow_add_one {p l n : ℕ} (hl3 : 3 ≤ l)
    (hqplus : p ∣ 2 ^ n + 1) :
    ggTwoSettledEitherLabelL p ⟨.twD, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.twD, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.twD, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.twD, l, n⟩ := by
  by_cases hl3' : l = 3
  · subst hl3'
    have hSL : ggTwoSettledLabelL p (⟨.twD, 3, n⟩ : LargeEvenLabel) := by
      apply Or.inr
      refine Or.inr (Or.inl ?_)
      exact ⟨Or.inr ⟨rfl, rfl⟩, hqplus⟩
    exact Or.inr (Or.inl hSL)
  · have hl4 : 4 ≤ l := by omega
    by_cases h3n : p = 3 ∧ n = 1
    · obtain ⟨rfl, rfl⟩ := h3n
      have hSL : ggTwoSettledLabelL 3 (⟨.twD, l, 1⟩ : LargeEvenLabel) := by
        apply Or.inr
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        exact ⟨rfl, Or.inr rfl, rfl, hl4⟩
      exact Or.inr (Or.inl hSL)
    · have hres : ggTwoResidualLabelL p (⟨.twD, l, n⟩ : LargeEvenLabel) := by
        refine Or.inr (Or.inl ?_)
        exact ⟨rfl, hl4, hqplus, h3n⟩
      exact Or.inr (Or.inr (Or.inr hres))

private theorem ggTwoCensus_label_L_of_twD {p l n : ℕ} (hl2 : 2 ≤ l)
    (hs : LargeEvenSplit p ⟨.twD, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.twD, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.twD, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.twD, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.twD, l, n⟩ := by
  simp [LargeEvenSplit, LargeEvenUntwisted] at hs
  by_cases hl2' : l = 2
  · subst hl2'
    have hsmall : ggThreeSmallLabel p (⟨.twD, 2, n⟩ : LargeEvenLabel) := by
      simp [ggThreeSmallLabel, GGRootGenSmallRankLabel]
    exact Or.inr (Or.inr (Or.inl hsmall))
  · have hl3 : 3 ≤ l := by omega
    rcases hs with hqplus | hqminus | ⟨hn, hp3⟩
    · exact ggTwoCensus_label_L_of_twD_dvd_pow_add_one hl3 hqplus
    · have hres : ggTwoResidualLabelL p (⟨.twD, l, n⟩ : LargeEvenLabel) := by
        refine Or.inl ?_
        exact ⟨Or.inr (Or.inr rfl), hl3, hqminus⟩
      exact Or.inr (Or.inr (Or.inr hres))
    · subst hn
      subst hp3
      exact ggTwoCensus_label_L_of_twD_dvd_pow_add_one hl3 (by norm_num)

private theorem ggTwoCensus_label_L_of_E6 {p l n : ℕ} (hs : LargeEvenSplit p ⟨.E6, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.E6, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.E6, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.E6, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.E6, l, n⟩ := by
  simp [LargeEvenSplit, LargeEvenUntwisted] at hs
  rcases hs with hq | ⟨hn, hp3⟩
  · have hres : ggTwoResidualLabelL p (⟨.E6, l, n⟩ : LargeEvenLabel) := by
      refine Or.inr (Or.inr (Or.inl ?_))
      exact Or.inl ⟨rfl, hq⟩
    exact Or.inr (Or.inr (Or.inr hres))
  · subst hn
    subst hp3
    have hres : ggTwoResidualLabelL 3 (⟨.E6, l, 1⟩ : LargeEvenLabel) := by
      refine Or.inr (Or.inr (Or.inl ?_))
      exact Or.inr ⟨Or.inl rfl, rfl, rfl⟩
    exact Or.inr (Or.inr (Or.inr hres))

private theorem ggTwoCensus_label_L_of_E7 {p l n : ℕ} (hs : LargeEvenSplit p ⟨.E7, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.E7, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.E7, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.E7, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.E7, l, n⟩ := by
  simp [LargeEvenSplit, LargeEvenUntwisted] at hs
  rcases hs with hq | ⟨hn, hp3⟩
  · have hSL : ggTwoSettledLabelL p (⟨.E7, l, n⟩ : LargeEvenLabel) := by
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
      exact ⟨Or.inl rfl, hq⟩
    exact Or.inr (Or.inl hSL)
  · subst hn
    subst hp3
    have hres : ggTwoResidualLabelL 3 (⟨.E7, l, 1⟩ : LargeEvenLabel) := by
      refine Or.inr (Or.inr (Or.inl ?_))
      exact Or.inr ⟨Or.inr (Or.inl rfl), rfl, rfl⟩
    exact Or.inr (Or.inr (Or.inr hres))

private theorem ggTwoCensus_label_L_of_E8 {p l n : ℕ} (hs : LargeEvenSplit p ⟨.E8, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.E8, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.E8, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.E8, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.E8, l, n⟩ := by
  simp [LargeEvenSplit, LargeEvenUntwisted] at hs
  rcases hs with hq | ⟨hn, hp3⟩
  · have hSL : ggTwoSettledLabelL p (⟨.E8, l, n⟩ : LargeEvenLabel) := by
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
      exact ⟨Or.inr rfl, hq⟩
    exact Or.inr (Or.inl hSL)
  · subst hn
    subst hp3
    have hres : ggTwoResidualLabelL 3 (⟨.E8, l, 1⟩ : LargeEvenLabel) := by
      refine Or.inr (Or.inr (Or.inl ?_))
      exact Or.inr ⟨Or.inr (Or.inr rfl), rfl, rfl⟩
    exact Or.inr (Or.inr (Or.inr hres))

private theorem ggTwoCensus_label_L_of_F4 {p l n : ℕ} (hs : LargeEvenSplit p ⟨.F4, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.F4, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.F4, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.F4, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.F4, l, n⟩ := by
  simp [LargeEvenSplit, LargeEvenUntwisted] at hs
  rcases hs with hq | ⟨hn, hp3⟩
  · have hSL : ggTwoSettledLabelL p (⟨.F4, l, n⟩ : LargeEvenLabel) := by
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))))
      exact ⟨rfl, hq⟩
    exact Or.inr (Or.inl hSL)
  · subst hn
    subst hp3
    have hSE : ggTwoSettledEitherLabelL 3 (⟨.F4, l, 1⟩ : LargeEvenLabel) := by
      refine Or.inr (Or.inr ?_)
      exact ⟨rfl, rfl, rfl⟩
    exact Or.inl hSE

private theorem ggTwoCensus_label_L_of_twE6 {p l n : ℕ} (hs : LargeEvenSplit p ⟨.twE6, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.twE6, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.twE6, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.twE6, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.twE6, l, n⟩ := by
  simp [LargeEvenSplit, LargeEvenUntwisted] at hs
  rcases hs with hqplus | ⟨hn, hp3⟩
  · have hres : ggTwoResidualLabelL p (⟨.twE6, l, n⟩ : LargeEvenLabel) := by
      refine Or.inr (Or.inr (Or.inr ?_))
      exact ⟨rfl, hqplus⟩
    exact Or.inr (Or.inr (Or.inr hres))
  · subst hn
    subst hp3
    have hqplus : (3 : ℕ) ∣ 2 ^ 1 + 1 := by norm_num
    have hres : ggTwoResidualLabelL 3 (⟨.twE6, l, 1⟩ : LargeEvenLabel) := by
      refine Or.inr (Or.inr (Or.inr ?_))
      exact ⟨rfl, hqplus⟩
    exact Or.inr (Or.inr (Or.inr hres))

private theorem ggTwoCensus_label_L_of_smallExcLabel {p l n : ℕ} {t : LargeEvenLieTag}
    (htag : t = .G2 ∨ t = .triD4 ∨ t = .twF4) (hphi : GGLabPhiOneTwo p ⟨t, l, n⟩)
    (hnot : ¬ GGTypeALabel p ⟨t, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨t, l, n⟩ ∨ ggTwoSettledLabelL p ⟨t, l, n⟩ ∨
      ggThreeSmallLabel p ⟨t, l, n⟩ ∨ ggTwoResidualLabelL p ⟨t, l, n⟩ :=
  Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨htag, hphi, hnot⟩))))

private theorem ggTwoCensus_label_L_of_G2 {p l n : ℕ} (hs : LargeEvenSplit p ⟨.G2, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.G2, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.G2, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.G2, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.G2, l, n⟩ :=
  ggTwoCensus_label_L_of_smallExcLabel (Or.inl rfl) (ggLabPhiOneTwo_of_largeEvenSplit hs)
    (by rintro (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩) <;> simp at h)

private theorem ggTwoCensus_label_L_of_twF4 {p l n : ℕ} (hs : LargeEvenSplit p ⟨.twF4, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.twF4, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.twF4, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.twF4, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.twF4, l, n⟩ :=
  ggTwoCensus_label_L_of_smallExcLabel (Or.inr (Or.inr rfl)) (ggLabPhiOneTwo_of_largeEvenSplit hs)
    (by rintro (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩) <;> simp at h)

private theorem ggTwoCensus_label_L_of_triD4 {p l n : ℕ} (hs : LargeEvenSplit p ⟨.triD4, l, n⟩) :
    ggTwoSettledEitherLabelL p ⟨.triD4, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.triD4, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.triD4, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.triD4, l, n⟩ :=
  ggTwoCensus_label_L_of_smallExcLabel (Or.inr (Or.inl rfl)) (ggLabPhiOneTwo_of_largeEvenSplit hs)
    (by rintro (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩) <;> simp at h)

private theorem ggTwoCensus_label_L_of_twB2 {p l n : ℕ} :
    ggTwoSettledEitherLabelL p ⟨.twB2, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.twB2, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.twB2, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.twB2, l, n⟩ :=
  Or.inr (Or.inr (Or.inl (by simp [ggThreeSmallLabel, GGRootGenSmallRankLabel])))

private theorem ggTwoCensus_label_L_of_B2der {p l n : ℕ} :
    ggTwoSettledEitherLabelL p ⟨.B2der, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.B2der, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.B2der, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.B2der, l, n⟩ :=
  Or.inr (Or.inr (Or.inl (by simp [ggThreeSmallLabel, GGRootGenSmallRankLabel])))

private theorem ggTwoCensus_label_L_of_G2der {p l n : ℕ} :
    ggTwoSettledEitherLabelL p ⟨.G2der, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.G2der, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.G2der, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.G2der, l, n⟩ :=
  Or.inr (Or.inr (Or.inl (by simp [ggThreeSmallLabel])))

private theorem ggTwoCensus_label_L_of_twF4der {p l n : ℕ} :
    ggTwoSettledEitherLabelL p ⟨.twF4der, l, n⟩ ∨ ggTwoSettledLabelL p ⟨.twF4der, l, n⟩ ∨
      ggThreeSmallLabel p ⟨.twF4der, l, n⟩ ∨ ggTwoResidualLabelL p ⟨.twF4der, l, n⟩ :=
  Or.inr (Or.inr (Or.inl (by simp [ggThreeSmallLabel])))

theorem ggTwoCensus_label_L {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenSplit p lab) :
    ggTwoSettledEitherLabelL p lab ∨ ggTwoSettledLabelL p lab ∨ ggThreeSmallLabel p lab ∨
      ggTwoResidualLabelL p lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  case A => exact ggTwoCensus_label_L_of_A hlab.2.1 hlab.2.2 hs
  case twA => exact ggTwoCensus_label_L_of_twA hlab.2.1 hlab.2.2 hs
  case B => exact ggTwoCensus_label_L_of_B hlab.2.1 hs
  case C => exact ggTwoCensus_label_L_of_C hlab.2.1 hs
  case D => exact ggTwoCensus_label_L_of_D hlab.2 hs
  case twD => exact ggTwoCensus_label_L_of_twD hlab.2 hs
  case E6 => exact ggTwoCensus_label_L_of_E6 hs
  case E7 => exact ggTwoCensus_label_L_of_E7 hs
  case E8 => exact ggTwoCensus_label_L_of_E8 hs
  case F4 => exact ggTwoCensus_label_L_of_F4 hs
  case twE6 => exact ggTwoCensus_label_L_of_twE6 hs
  case G2 => exact ggTwoCensus_label_L_of_G2 hs
  case twB2 => exact ggTwoCensus_label_L_of_twB2
  case twF4 => exact ggTwoCensus_label_L_of_twF4 hs
  case triD4 => exact ggTwoCensus_label_L_of_triD4 hs
  case B2der => exact ggTwoCensus_label_L_of_B2der
  case G2der => exact ggTwoCensus_label_L_of_G2der
  case twF4der => exact ggTwoCensus_label_L_of_twF4der

end CFSG.StandardType

end
