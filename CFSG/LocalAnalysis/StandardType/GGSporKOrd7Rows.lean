module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Search
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7PSL
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7PSp
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7PSU
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7POmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7POmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7L2
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7U33
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7D4
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7G2
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7F4
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7TrialityD4
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7TwistedE6
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Suzuki
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Tits

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

theorem ord7Row_of_dvd
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hd : labOrd lab ∣ 4154781481226426191177580544000000) : Ord7Row lab := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hs1, hs2⟩ := ord7_search_B hlab hd
  cases t <;> simp only [Ord7Row, markTag, markRank, markChar, markDeg]
  ·
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨hn, hl1, hl2⟩ := hlab
    have h7 : ¬ 7 ∣ n := by
      have h := (hs2 (by simp) (by simp [markChar])).1
      simpa only [markDeg] using h
    by_cases hl : l = 1
    · rw [hl]
      exact ord7Param_PSL_two Nat.prime_two h7
    · have hl2' : 2 ≤ l := by omega
      have h7q : ¬ 7 ∣ 2 ^ n - 1 := by
        have h := (hs2 (by simp) (by simp [markChar])).2.1 rfl (by simp only [markRank]; omega)
        simpa only [markDeg] using h
      exact ord7Param_PSL h7 h7q (by omega)
  ·
    simp only [LargeEvenInLambda2] at hlab
    have h7 : ¬ 7 ∣ n := by
      have h := (hs2 (by simp) (by simp [markChar])).1
      simpa only [markDeg] using h
    exact ord7Param_PSU h7
  ·
    have h7 : ¬ 7 ∣ n := by
      have h := (hs2 (by simp) (by simp [markChar])).1
      simpa only [markDeg] using h
    exact ord7Param_PSp h7
  ·
    have h7 : ¬ 7 ∣ n := by
      have h := (hs2 (by simp) (by simp [markChar])).1
      simpa only [markDeg] using h
    exact ord7Param_PSp h7
  ·
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hl3⟩ := hlab
    have h7 : ¬ 7 ∣ n := by
      have h := (hs2 (by simp) (by simp [markChar])).1
      simpa only [markDeg] using h
    by_cases h3 : l = 3
    · simp only [if_pos h3]
      have h7q : ¬ 7 ∣ 2 ^ n - 1 := by
        have h := (hs2 (by simp) (by simp [markChar])).2.1
          (by simp only [markTag, if_pos h3])
          (by simp only [markRank, if_pos h3]; norm_num)
        simpa only [markDeg] using h
      exact ord7Param_PSL h7 h7q (by norm_num)
    · simp only [if_neg h3]
      by_cases h4 : l = 4
      · have hn1 : n = 1 := by
          have h := (hs2 (by simp) (by simp [markChar])).2.2.2.2.2 rfl h4
          simpa only [markDeg] using h
        rw [h4, hn1]
        exact ord7Param_D4_two
      · have hl5 : 5 ≤ l := by omega
        exact ord7Param_POmegaPlus h7 (by omega)
  ·
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hl2⟩ := hlab
    by_cases h2 : l = 2
    · simp only [if_pos h2]
      have h7 : ¬ 7 ∣ 2 * n := by
        have h := (hs2 (by simp) (by simp [markChar])).1
        simpa only [markDeg, if_pos h2] using h
      exact ord7Param_PSL_two Nat.prime_two h7
    · have hl3 : 3 ≤ l := by omega
      by_cases h3 : l = 3
      · simp only [if_neg h2, if_pos h3]
        have h7 : ¬ 7 ∣ n := by
          have h := (hs2 (by simp) (by simp [markChar])).1
          simpa only [markDeg, if_neg h2] using h
        exact ord7Param_PSU h7
      · simp only [if_neg h2, if_neg h3]
        have h7 : ¬ 7 ∣ n := by
          have h := (hs2 (by simp) (by simp [markChar])).1
          simpa only [markDeg, if_neg h2] using h
        exact ord7Param_POmegaMinus h7
  ·
    exact absurd rfl ((hs2 (by simp) (by simp [markChar])).2.2.1)
  ·
    exact absurd rfl ((hs2 (by simp) (by simp [markChar])).2.2.2.1)
  ·
    exact absurd rfl ((hs2 (by simp) (by simp [markChar])).2.2.2.2.1)
  ·
    have h7 : ¬ 7 ∣ n := by
      have h := (hs2 (by simp) (by simp [markChar])).1
      simpa only [markDeg] using h
    exact ord7Param_F4 h7
  ·
    have h7 : ¬ 7 ∣ n := by
      have h := (hs2 (by simp) (by simp [markChar])).1
      simpa only [markDeg] using h
    exact ord7Param_twistedE6 h7
  ·
    have h7 : ¬ 7 ∣ n := by
      have h := (hs2 (by simp) (by simp [markChar])).1
      simpa only [markDeg] using h
    exact ord7Param_trialityD4 h7
  ·
    have h7 : ¬ 7 ∣ n := by
      have h := (hs2 (by simp) (by simp [markChar])).1
      simpa only [markDeg] using h
    exact ord7Param_G2 h7
  ·
    have h7 : ¬ 7 ∣ n := by
      have h := (hs2 (by simp) (by simp [markChar])).1
      simpa only [markDeg] using h
    exact ord7Param_twistedB2 h7
  ·
    exact absurd rfl hs1
  ·
    exact ord7Param_PSL_two Nat.prime_three (by norm_num)
  ·
    exact ord7Param_U33
  ·
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, -, hn1⟩ := hlab
    rw [hn1]
    exact ord7Param_Tits

end CFSG.StandardType.SporadicShape
