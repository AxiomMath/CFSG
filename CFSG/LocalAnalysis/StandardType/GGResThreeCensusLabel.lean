module

public import CFSG.LocalAnalysis.StandardType.GGResThreeSettledDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggThreeCensus_label_L {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenSplit p lab) :
    ggThreeNonsingBaseLabel p lab ∨ ggThreeSettledLabelL p lab ∨ ggThreeSmallLabel p lab ∨
      ggThreeSettledE6LabelL p lab ∨ ggThreeResidualLabelL p lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  case A =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hq | ⟨hn, hp3⟩
    · exact Or.inr (Or.inl (Or.inl ⟨rfl, hq⟩))
    · subst hn
      subst hp3
      obtain ⟨-, hl1, himp⟩ := hlab
      have hl2 : 2 ≤ l := by
        by_contra h
        have h1 : l = 1 := by omega
        exact absurd (himp h1) (by omega)
      by_cases hl4 : l ≤ 4
      · have hsmall : ggThreeSmallLabel 3 ⟨.A, l, 1⟩ := by
          refine Or.inr (Or.inr (Or.inl ?_))
          exact ⟨rfl, rfl, Or.inl ⟨rfl, hl4⟩⟩
        exact Or.inr (Or.inr (Or.inl hsmall))
      · have hl5or : l = 5 ∨ 6 ≤ l := by omega
        rcases hl5or with hl5 | hl6
        · subst hl5
          have hns : ¬ ggSingularBaseLabel 3 (⟨.A, 5, 1⟩ : LargeEvenLabel) := by
            norm_num [ggSingularBaseLabel]
          exact Or.inl (Or.inl ⟨⟨_, _, _, _, _,
            GGTBTorRowAt.relA5 rfl (Or.inl ⟨rfl, by norm_num⟩)⟩, hns⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, hl6⟩)))
  case twA =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hqplus | ⟨hn, hp3⟩
    · obtain ⟨-, hl2, -⟩ := hlab
      by_cases hl2' : l = 2
      · subst hl2'
        have hsmall : ggThreeSmallLabel p ⟨.twA, 2, n⟩ := by
          simp [ggThreeSmallLabel, GGRootGenSmallRankLabel]
        exact Or.inr (Or.inr (Or.inl hsmall))
      · by_cases hl3 : l = 3
        · subst hl3
          have h4 : ¬ p ∣ 3 + 1 := by
            intro h
            have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (by simpa using h)
            exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
          have hm : p ∣ ggTorM (⟨.twA, 3, n⟩ : LargeEvenLabel) := by
            simpa [ggTorM] using hqplus
          refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
            GGTBTorRowAt.aInd (Or.inr rfl) h4 hm⟩, ?_⟩)
          simp [ggSingularBaseLabel, h4]
        · have hl4 : 4 ≤ l := by omega
          exact Or.inr (Or.inl (Or.inr (Or.inl ⟨rfl, hl4, hqplus⟩)))
    · subst hn
      subst hp3
      obtain ⟨-, hl2, himp⟩ := hlab
      have hl3 : 3 ≤ l := by
        by_contra h
        have h2 : l = 2 := by omega
        exact absurd (himp h2) (by omega)
      by_cases hl3' : l = 3
      · subst hl3'
        have hm : (3 : ℕ) ∣ ggTorM (⟨.twA, 3, 1⟩ : LargeEvenLabel) := by
          norm_num [ggTorM]
        have h4 : ¬ (3 : ℕ) ∣ 3 + 1 := by norm_num
        refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.aInd (Or.inr rfl) h4 hm⟩, ?_⟩)
        simp [ggSingularBaseLabel, h4]
      · have hl4 : 4 ≤ l := by omega
        exact Or.inr (Or.inl (Or.inr (Or.inl ⟨rfl, hl4, by norm_num⟩)))
  case B =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := by
      rcases hs with hq | ⟨hn, hp3⟩
      · exact hq.mul_right _
      · subst hn
        subst hp3
        norm_num
    refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
      GGTBTorRowAt.c (Or.inl rfl) hprod⟩, ?_⟩)
    simp [ggSingularBaseLabel]
  case C =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := by
      rcases hs with hq | ⟨hn, hp3⟩
      · exact hq.mul_right _
      · subst hn
        subst hp3
        norm_num
    refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
      GGTBTorRowAt.c (Or.inr rfl) hprod⟩, ?_⟩)
    simp [ggSingularBaseLabel]
  case D =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hq | ⟨hn, hp3⟩
    · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
        GGTBTorRowAt.d (Or.inl ⟨rfl, Or.inl hq⟩)⟩, ?_⟩)
      simp [ggSingularBaseLabel]
    · subst hn
      subst hp3
      rcases Nat.even_or_odd l with he | ho
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.d (Or.inl ⟨rfl, Or.inr ⟨by norm_num, he⟩⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.relD (Or.inl ⟨rfl, by norm_num, ho⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
  case twD =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hqplus | hqminus | ⟨hn, hp3⟩
    · rcases Nat.even_or_odd l with he | ho
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inr ⟨hqplus, he⟩⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.d (Or.inr ⟨rfl, hqplus, ho⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
    · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
        GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inl hqminus⟩)⟩, ?_⟩)
      simp [ggSingularBaseLabel]
    · subst hn
      subst hp3
      rcases Nat.even_or_odd l with he | ho
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inr ⟨by norm_num, he⟩⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.d (Or.inr ⟨rfl, by norm_num, ho⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
  case E6 =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hq | ⟨hn, hp3⟩
    · by_cases hp3 : p = 3
      · subst hp3
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, hq⟩⟩)))
      · have hm : p ∣ ggTorM (⟨.E6, 0, n⟩ : LargeEvenLabel) := by
          simpa [ggTorM] using hq
        refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.e6Ind hp3 (Or.inl rfl) hm⟩, ?_⟩)
        simp [ggSingularBaseLabel, hp3]
    · subst hn
      subst hp3
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr ⟨rfl, by norm_num⟩))⟩)))
  case E7 =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := by
      rcases hs with hq | ⟨hn, hp3⟩
      · exact hq.mul_right _
      · subst hn
        subst hp3
        norm_num
    refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
      GGTBTorRowAt.e7 rfl hprod⟩, ?_⟩)
    simp [ggSingularBaseLabel]
  case E8 =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := by
      rcases hs with hq | ⟨hn, hp3⟩
      · exact hq.mul_right _
      · subst hn
        subst hp3
        norm_num
    by_cases hp3 : p = 3
    · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
        GGTBTorRowAt.e8Three rfl hp3⟩, ?_⟩)
      simp [ggSingularBaseLabel]
    · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
        GGTBTorRowAt.e8Ind hp3 rfl hprod⟩, ?_⟩)
      simp [ggSingularBaseLabel]
  case twE6 =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hqplus | ⟨hn, hp3⟩
    · by_cases hp3 : p = 3
      · subst hp3
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, hqplus⟩)⟩)))
      · have hm : p ∣ ggTorM (⟨.twE6, l, n⟩ : LargeEvenLabel) := by
          simpa [ggTorM] using hqplus
        refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.e6Ind hp3 (Or.inr rfl) hm⟩, ?_⟩)
        simp [ggSingularBaseLabel]
    · subst hn
      subst hp3
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, by norm_num⟩)⟩)))
  case triD4 =>
    have hphi : GGLabPhiOneTwo p ⟨.triD4, l, n⟩ := ggLabPhiOneTwo_of_largeEvenSplit hs
    have hnot : ¬ GGTypeALabel p ⟨.triD4, l, n⟩ := by
      rintro (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩) <;> simp at h
    have hsmall : ggThreeSmallLabel p ⟨.triD4, l, n⟩ := by
      refine Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), hphi, hnot⟩)
    exact Or.inr (Or.inr (Or.inl hsmall))
  case F4 =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hq | ⟨hn, hp3⟩
    · by_cases hp3 : p = 3
      · have hnot : ¬ (p = 3 ∧ p ∣ 2 ^ n + 1) := by
          rintro ⟨rfl, hplus⟩
          have h2 : (3 : ℕ) ∣ 2 := by
            have hsub := Nat.dvd_sub hplus hq
            have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
            have hdiff : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
            rwa [hdiff] at hsub
          norm_num at h2
        refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.f4 rfl (hq.mul_right _) hnot⟩, ?_⟩)
        simp [ggSingularBaseLabel]
      · have hnot : ¬ (p = 3 ∧ p ∣ 2 ^ n + 1) := by
          rintro ⟨h, -⟩
          exact hp3 h
        refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.f4 rfl (hq.mul_right _) hnot⟩, ?_⟩)
        simp [ggSingularBaseLabel]
    · subst hn
      subst hp3
      exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl, by norm_num⟩))
  case G2 =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hq | ⟨hn, hp3⟩
    · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
        GGTBTorRowAt.g2 rfl hq⟩, ?_⟩)
      simp [ggSingularBaseLabel]
    · subst hn
      omega
  case twB2 =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hq | ⟨hn, hp3⟩
    · have hsmall : ggThreeSmallLabel p ⟨.twB2, l, n⟩ := by
        simp [ggThreeSmallLabel, GGRootGenSmallRankLabel]
      exact Or.inr (Or.inr (Or.inl hsmall))
    · subst hn
      omega
  case twF4 =>
    simp [LargeEvenInLambda2, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hqplus | ⟨hn, hp3⟩
    · have hphi : GGLabPhiOneTwo p ⟨.twF4, l, n⟩ := by
        unfold GGLabPhiOneTwo
        have hpow : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
        rw [hpow]
        exact OrthRest.dvd_sq_sub_one (Or.inl hqplus)
      have hnot : ¬ GGTypeALabel p ⟨.twF4, l, n⟩ := by
        rintro (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩) <;> simp at h
      have hsmall : ggThreeSmallLabel p ⟨.twF4, l, n⟩ := by
        refine Or.inr (Or.inl ⟨Or.inr (Or.inr rfl), hphi, hnot⟩)
      exact Or.inr (Or.inr (Or.inl hsmall))
    · subst hn
      omega
  case B2der =>
    have hsmall : ggThreeSmallLabel p ⟨.B2der, l, n⟩ := by
      simp [ggThreeSmallLabel, GGRootGenSmallRankLabel]
    exact Or.inr (Or.inr (Or.inl hsmall))
  case G2der =>
    have hsmall : ggThreeSmallLabel p ⟨.G2der, l, n⟩ := by
      simp [ggThreeSmallLabel]
    exact Or.inr (Or.inr (Or.inl hsmall))
  case twF4der =>
    have hsmall : ggThreeSmallLabel p ⟨.twF4der, l, n⟩ := by
      simp [ggThreeSmallLabel]
    exact Or.inr (Or.inr (Or.inl hsmall))

theorem ggThreeCensus_label_K {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    {c : Prop} (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenHalfSplit p lab c) :
    ggThreeNonsingBaseLabel p lab ∨ ggThreeSettledLabelK p lab ∨ ggThreeSettledE6LabelK p lab ∨
      ggThreeSettledLinTwoLabelK p lab ∨ ggThreeSettledLinNsLabelK p lab ∨
      ggThreeSettledLinSplitLabelK p lab ∨ ggThreeResidualLabelK p lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  case A =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with (hq | ⟨hn, hp3⟩) | ⟨hl5, hn2, -, hp5⟩ | ⟨hl8, hn1, hp7⟩
    · by_cases hl4 : 4 ≤ l
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hl4, hq⟩)))))
      · obtain ⟨-, hl1, himp⟩ := hlab
        by_cases hl3 : l = 3
        · subst hl3
          have h4 : ¬ p ∣ 3 + 1 := by
            intro h
            have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (by simpa using h)
            exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
          have hm : p ∣ ggTorM (⟨.A, 3, n⟩ : LargeEvenLabel) := by
            simpa [ggTorM] using hq
          refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
            GGTBTorRowAt.aInd (Or.inl rfl) h4 hm⟩, ?_⟩)
          simp [ggSingularBaseLabel, h4]
        · have hl12 : l = 1 ∨ l = 2 := by omega
          rcases hl12 with rfl | rfl
          · have hsmall : ggThreeSmallLabel p ⟨.A, 1, n⟩ := by
              simp [ggThreeSmallLabel, GGRootGenSmallRankLabel]
            exact Or.inr (Or.inl (Or.inl hsmall))
          · have hsmall : ggThreeSmallLabel p ⟨.A, 2, n⟩ := by
              simp [ggThreeSmallLabel, GGRootGenSmallRankLabel]
            exact Or.inr (Or.inl (Or.inl hsmall))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp3, rfl, hn⟩)))
    · subst hn2
      subst hp5
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by norm_num⟩))))
    · exact Or.inr (Or.inl (Or.inr ⟨hp7, Or.inl ⟨rfl, hl8, hn1⟩⟩))
  case twA =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with (hqplus | ⟨hn, hp3⟩) | ⟨hl5, hqminus⟩
    · obtain ⟨-, hl2, -⟩ := hlab
      by_cases hl2' : l = 2
      · subst hl2'
        have hsmall : ggThreeSmallLabel p ⟨.twA, 2, n⟩ := by
          simp [ggThreeSmallLabel, GGRootGenSmallRankLabel]
        exact Or.inr (Or.inl (Or.inl hsmall))
      · by_cases hl3 : l = 3
        · subst hl3
          have h4 : ¬ p ∣ 3 + 1 := by
            intro h
            have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (by simpa using h)
            exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
          have hm : p ∣ ggTorM (⟨.twA, 3, n⟩ : LargeEvenLabel) := by
            simpa [ggTorM] using hqplus
          refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
            GGTBTorRowAt.aInd (Or.inr rfl) h4 hm⟩, ?_⟩)
          simp [ggSingularBaseLabel, h4]
        · have hl4 : 4 ≤ l := by omega
          by_cases hpr : p ∣ l + 1
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨rfl, hl4, hpr, hqplus⟩)))))
          · have hm : p ∣ ggTorM (⟨.twA, l, n⟩ : LargeEvenLabel) := by
              simpa [ggTorM] using hqplus
            refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
              GGTBTorRowAt.aInd (Or.inr rfl) hpr hm⟩, ?_⟩)
            simp [ggSingularBaseLabel, hpr]
    · subst hn
      subst hp3
      obtain ⟨-, hl2, himp⟩ := hlab
      have hqplus : (3 : ℕ) ∣ 2 ^ 1 + 1 := by norm_num
      have hl3 : 3 ≤ l := by
        by_contra h
        have h2 : l = 2 := by omega
        exact absurd (himp h2) (by omega)
      by_cases hl3' : l = 3
      · subst hl3'
        have hm : (3 : ℕ) ∣ ggTorM (⟨.twA, 3, 1⟩ : LargeEvenLabel) := by
          norm_num [ggTorM]
        have h4 : ¬ (3 : ℕ) ∣ 3 + 1 := by norm_num
        refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.aInd (Or.inr rfl) h4 hm⟩, ?_⟩)
        simp [ggSingularBaseLabel, h4]
      · have hl4 : 4 ≤ l := by omega
        by_cases hpr : (3 : ℕ) ∣ l + 1
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨rfl, hl4, hpr, hqplus⟩)))))
        · have hm : (3 : ℕ) ∣ ggTorM (⟨.twA, l, 1⟩ : LargeEvenLabel) := by
            simp [ggTorM]
          refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
            GGTBTorRowAt.aInd (Or.inr rfl) hpr hm⟩, ?_⟩)
          simp [ggSingularBaseLabel, hpr]
    · have hsplit : GGTwASplitLabel p ⟨.twA, l, n⟩ := by
        refine ⟨rfl, ?_, hqminus⟩
        simp [hl5]
      exact Or.inl (Or.inr (Or.inr hsplit))
  case B =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := by
      rcases hs with (hq | ⟨hn, hp3⟩) | hqplus
      · exact hq.mul_right _
      · subst hn
        subst hp3
        norm_num
      · exact hqplus.mul_left _
    refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
      GGTBTorRowAt.c (Or.inl rfl) hprod⟩, ?_⟩)
    simp [ggSingularBaseLabel]
  case C =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := by
      rcases hs with hq | ⟨hn, hp3⟩
      · exact hq.mul_right _
      · subst hn
        subst hp3
        norm_num
    refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
      GGTBTorRowAt.c (Or.inr rfl) hprod⟩, ?_⟩)
    simp [ggSingularBaseLabel]
  case D =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with (hq | ⟨hn, hp3⟩) | hqplus
    · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
        GGTBTorRowAt.d (Or.inl ⟨rfl, Or.inl hq⟩)⟩, ?_⟩)
      simp [ggSingularBaseLabel]
    · subst hn
      subst hp3
      rcases Nat.even_or_odd l with he | ho
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.d (Or.inl ⟨rfl, Or.inr ⟨by norm_num, he⟩⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.relD (Or.inl ⟨rfl, by norm_num, ho⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
    · rcases Nat.even_or_odd l with he | ho
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.d (Or.inl ⟨rfl, Or.inr ⟨hqplus, he⟩⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.relD (Or.inl ⟨rfl, hqplus, ho⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
  case twD =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hqplus | hqminus | ⟨hn, hp3⟩
    · rcases Nat.even_or_odd l with he | ho
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inr ⟨hqplus, he⟩⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.d (Or.inr ⟨rfl, hqplus, ho⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
    · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
        GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inl hqminus⟩)⟩, ?_⟩)
      simp [ggSingularBaseLabel]
    · subst hn
      subst hp3
      rcases Nat.even_or_odd l with he | ho
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inr ⟨by norm_num, he⟩⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.d (Or.inr ⟨rfl, by norm_num, ho⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
  case E6 =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with (hq | ⟨hn, hp3⟩) | ⟨hn1, hp7⟩
    · by_cases hp3 : p = 3
      · subst hp3
        exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, hq⟩⟩))
      · have hm : p ∣ ggTorM (⟨.E6, l, n⟩ : LargeEvenLabel) := by
          simpa [ggTorM] using hq
        refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.e6Ind hp3 (Or.inl rfl) hm⟩, ?_⟩)
        simp [ggSingularBaseLabel, hp3]
    · subst hn
      subst hp3
      exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr ⟨rfl, by norm_num⟩))⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨hp7, Or.inr ⟨rfl, hn1⟩⟩))
  case E7 =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := by
      rcases hs with (hq | ⟨hn, hp3⟩) | hqplus
      · exact hq.mul_right _
      · subst hn
        subst hp3
        norm_num
      · exact hqplus.mul_left _
    refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
      GGTBTorRowAt.e7 rfl hprod⟩, ?_⟩)
    simp [ggSingularBaseLabel]
  case E8 =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    have hprod : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := by
      rcases hs with (hq | ⟨hn, hp3⟩) | hqplus
      · exact hq.mul_right _
      · subst hn
        subst hp3
        norm_num
      · exact hqplus.mul_left _
    by_cases hp3 : p = 3
    · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
        GGTBTorRowAt.e8Three rfl hp3⟩, ?_⟩)
      simp [ggSingularBaseLabel]
    · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
        GGTBTorRowAt.e8Ind hp3 rfl hprod⟩, ?_⟩)
      simp [ggSingularBaseLabel]
  case twE6 =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with (hqplus | ⟨hn, hp3⟩) | hqminus
    · by_cases hp3 : p = 3
      · subst hp3
        exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, hqplus⟩)⟩))
      · have hm : p ∣ ggTorM (⟨.twE6, l, n⟩ : LargeEvenLabel) := by
          simpa [ggTorM] using hqplus
        refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.e6Ind hp3 (Or.inr rfl) hm⟩, ?_⟩)
        simp [ggSingularBaseLabel]
    · subst hn
      subst hp3
      exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, by norm_num⟩)⟩))
    · by_cases hp3 : p = 3
      · subst hp3
        exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, hqminus⟩))⟩))
      · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.relE6 hp3 (Or.inr ⟨rfl, hqminus⟩)⟩, ?_⟩)
        simp [ggSingularBaseLabel]
  case F4 =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with (hq | ⟨hn, hp3⟩) | hqplus
    · by_cases hp3 : p = 3
      · have hnot : ¬ (p = 3 ∧ p ∣ 2 ^ n + 1) := by
          rintro ⟨rfl, hplus⟩
          have h2 : (3 : ℕ) ∣ 2 := by
            have hsub := Nat.dvd_sub hplus hq
            have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
            have hdiff : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
            rwa [hdiff] at hsub
          norm_num at h2
        refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.f4 rfl (hq.mul_right _) hnot⟩, ?_⟩)
        simp [ggSingularBaseLabel]
      · have hnot : ¬ (p = 3 ∧ p ∣ 2 ^ n + 1) := by
          rintro ⟨h, -⟩
          exact hp3 h
        refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.f4 rfl (hq.mul_right _) hnot⟩, ?_⟩)
        simp [ggSingularBaseLabel]
    · subst hn
      subst hp3
      exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl, by norm_num⟩))
    · by_cases hp3 : p = 3
      · subst hp3
        exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl, hqplus⟩))
      · have hnot : ¬ (p = 3 ∧ p ∣ 2 ^ n + 1) := by
          rintro ⟨h, -⟩
          exact hp3 h
        refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
          GGTBTorRowAt.f4 rfl (hqplus.mul_left _) hnot⟩, ?_⟩)
        simp [ggSingularBaseLabel]
  case G2 =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hq | ⟨hn, hp3⟩
    · refine Or.inl (Or.inl ⟨⟨_, _, _, _, _,
        GGTBTorRowAt.g2 rfl hq⟩, ?_⟩)
      simp [ggSingularBaseLabel]
    · subst hn
      omega
  case twB2 =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hq | ⟨hn, hp3⟩
    · have hsmall : ggThreeSmallLabel p ⟨.twB2, l, n⟩ := by
        simp [ggThreeSmallLabel, GGRootGenSmallRankLabel]
      exact Or.inr (Or.inl (Or.inl hsmall))
    · subst hn
      omega
  case twF4 =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    rcases hs with hqplus | ⟨hn, hp3⟩
    · have hphi : GGLabPhiOneTwo p ⟨.twF4, l, n⟩ := by
        unfold GGLabPhiOneTwo
        have hpow : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
        rw [hpow]
        exact OrthRest.dvd_sq_sub_one (Or.inl hqplus)
      have hnot : ¬ GGTypeALabel p ⟨.twF4, l, n⟩ := by
        rintro (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩) <;> simp at h
      have hsmall : ggThreeSmallLabel p ⟨.twF4, l, n⟩ := by
        refine Or.inr (Or.inl ⟨Or.inr (Or.inr rfl), hphi, hnot⟩)
      exact Or.inr (Or.inl (Or.inl hsmall))
    · subst hn
      omega
  case triD4 =>
    simp [LargeEvenInLambda2, LargeEvenHalfSplit, LargeEvenSplit, LargeEvenUntwisted] at hlab hs
    have hnot : ¬ GGTypeALabel p ⟨.triD4, l, n⟩ := by
      rintro (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩) <;> simp at h
    have hsmall : ggThreeSmallLabel p ⟨.triD4, l, n⟩ := by
      refine Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), ?_, hnot⟩)
      unfold GGLabPhiOneTwo
      rcases hs with hq | ⟨hn, hp3⟩
      · have hpow : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
        rw [hpow]
        exact OrthRest.dvd_sq_sub_one (Or.inr hq)
      · subst hn
        subst hp3
        norm_num
    exact Or.inr (Or.inl (Or.inl hsmall))
  case B2der =>
    have hsmall : ggThreeSmallLabel p ⟨.B2der, l, n⟩ := by
      simp [ggThreeSmallLabel, GGRootGenSmallRankLabel]
    exact Or.inr (Or.inl (Or.inl hsmall))
  case G2der =>
    have hsmall : ggThreeSmallLabel p ⟨.G2der, l, n⟩ := by
      simp [ggThreeSmallLabel]
    exact Or.inr (Or.inl (Or.inl hsmall))
  case twF4der =>
    have hsmall : ggThreeSmallLabel p ⟨.twF4der, l, n⟩ := by
      simp [ggThreeSmallLabel]
    exact Or.inr (Or.inl (Or.inl hsmall))

end CFSG.StandardType

end
