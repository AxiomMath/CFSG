module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBExcPlus
public import CFSG.LocalAnalysis.StandardType.GGFrameTBTwE6
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
import CFSG.LocalAnalysis.StandardType.GGFrameTBSmall
import CFSG.LocalAnalysis.StandardType.GGFrameTBSU
import CFSG.LocalAnalysis.StandardType.GGFrameTBSUDvd
import CFSG.LocalAnalysis.StandardType.GGFrameTBSp
import CFSG.LocalAnalysis.StandardType.GGFrameTBOmega
import CFSG.LocalAnalysis.StandardType.GGFrameTBTw

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly

section Classical


private lemma frameTBHolds_A {m : ℕ} (hΛ : LargeEvenInLambda2 ⟨.A, m, 1⟩) :
    LargeEvenLabelAll ⟨.A, m, 1⟩ (frameTBBody ⟨.A, m, 1⟩) := by
  have hm1 : 1 ≤ m := hΛ.2.1
  have hne : m ≠ 1 := by
    intro hm
    have h21 : 2 ≤ 1 := hΛ.2.2 hm
    omega
  by_cases hm4 : m ≤ 4
  · exact frameTBBody_twoThreeSmall ⟨rfl, rfl, Or.inl ⟨rfl, hm4⟩⟩
  · obtain ⟨r, ε, hr, hε, rfl⟩ : ∃ r ε, 3 ≤ r ∧ ε ≤ 1 ∧ m = 2 * r - 1 + ε :=
      ⟨(m + 1) / 2, m + 1 - 2 * ((m + 1) / 2), by omega, by omega, by omega⟩
    exact frameTBBody_slHalf hr hε

private lemma frameTBHolds_twA {m : ℕ} (hΛ : LargeEvenInLambda2 ⟨.twA, m, 1⟩) :
    LargeEvenLabelAll ⟨.twA, m, 1⟩ (frameTBBody ⟨.twA, m, 1⟩) := by
  have hm2 : 2 ≤ m := hΛ.2.1
  have hne : m ≠ 2 := by
    intro hm
    have h21 : 2 ≤ 1 := hΛ.2.2 hm
    omega
  by_cases hm5 : m ≤ 5
  · exact frameTBBody_twA_small (by omega) hm5
  · have hm6 : 6 ≤ m := by omega
    by_cases h3 : 3 ∣ m + 1
    · have hm8 : 8 ≤ m := by
        obtain ⟨k, hk⟩ := h3
        omega
      exact frameTBBody_suDvd hm8 h3
    · exact frameTBBody_suCoprime (by omega) h3

private lemma frameTBHolds_B {m : ℕ} (hΛ : LargeEvenInLambda2 ⟨.B, m, 1⟩) :
    LargeEvenLabelAll ⟨.B, m, 1⟩ (frameTBBody ⟨.B, m, 1⟩) :=
  frameTBBody_sp hΛ rfl (Or.inl rfl)

private lemma frameTBHolds_C {m : ℕ} (hΛ : LargeEvenInLambda2 ⟨.C, m, 1⟩) :
    LargeEvenLabelAll ⟨.C, m, 1⟩ (frameTBBody ⟨.C, m, 1⟩) :=
  frameTBBody_sp hΛ rfl (Or.inr rfl)

private lemma frameTBHolds_D {m : ℕ} (hΛ : LargeEvenInLambda2 ⟨.D, m, 1⟩) :
    LargeEvenLabelAll ⟨.D, m, 1⟩ (frameTBBody ⟨.D, m, 1⟩) := by
  have hm3 : 3 ≤ m := hΛ.2
  by_cases h3 : m = 3
  · subst h3
    exact frameTBBody_twoThreeSmall ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
  · have hm4 : 4 ≤ m := by omega
    obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
    have hr : 3 ≤ r := by omega
    rcases Nat.even_or_odd r with hev | hodd
    · exact frameTBBody_omPlusHalf hr hev
    · exact frameTBBody_omPlusFull hr hodd

private lemma frameTBHolds_twD {m : ℕ} (hΛ : LargeEvenInLambda2 ⟨.twD, m, 1⟩) :
    LargeEvenLabelAll ⟨.twD, m, 1⟩ (frameTBBody ⟨.twD, m, 1⟩) := by
  have hm2 : 2 ≤ m := hΛ.2
  by_cases h2 : m = 2
  · subst h2
    exact frameTBBody_linearTwo hΛ (Or.inr ⟨rfl, rfl⟩)
  · by_cases h3 : m = 3
    · subst h3
      exact frameTBBody_twD_three
    · have hm4 : 4 ≤ m := by omega
      obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
      have hr : 3 ≤ r := by omega
      rcases Nat.even_or_odd r with hev | hodd
      · have hr4 : 4 ≤ r := by
          obtain ⟨k, hk⟩ := hev
          omega
        exact frameTBBody_omMinusFull hr4 hev
      · exact frameTBBody_omMinusHalf hr hodd

end Classical

section Exceptional


private lemma frameTBHolds_twE6 {m : ℕ} :
    LargeEvenLabelAll ⟨.twE6, m, 1⟩ (frameTBBody ⟨.twE6, m, 1⟩) :=
  frameTBBody_twE6 rfl rfl

private lemma frameTBHolds_E7 {m : ℕ} :
    LargeEvenLabelAll ⟨.E7, m, 1⟩ (frameTBBody ⟨.E7, m, 1⟩) :=
  frameTBBody_E7 rfl rfl

private lemma frameTBHolds_E8 {m : ℕ} :
    LargeEvenLabelAll ⟨.E8, m, 1⟩ (frameTBBody ⟨.E8, m, 1⟩) :=
  frameTBBody_E8 rfl rfl

end Exceptional

theorem ggFrameTBNumerologyInput_holds :
    GGFrameTBNumerologyInput := by
  rw [ggFrameTBNumerologyInput_iff]
  refine ⟨?_, fun lab _ hn ht => ?_⟩
  swap
  · obtain ⟨t, m, k⟩ := lab
    dsimp only at hn ht
    subst ht hn
    exact largeEvenLabelAll_torusLift_excPlus Nat.prime_three (by norm_num)
      ⟨Or.inr (Or.inl rfl), by norm_num⟩
  rintro ⟨tag, m, n⟩ hΛ hn ht
  dsimp only at hn ht ⊢
  subst hn
  cases tag
  · exact frameTBHolds_A hΛ
  · exact frameTBHolds_twA hΛ
  · exact frameTBHolds_B hΛ
  · exact frameTBHolds_C hΛ
  · exact frameTBHolds_D hΛ
  · exact frameTBHolds_twD hΛ
  · simp [frameTagTabled] at ht
  · exact frameTBHolds_E7
  · exact frameTBHolds_E8
  · simp [frameTagTabled] at ht
  · exact frameTBHolds_twE6
  · simp [frameTagTabled] at ht
  · simp [frameTagTabled] at ht
  · simp [frameTagTabled] at ht
  · simp [frameTagTabled] at ht
  · simp [frameTagTabled] at ht
  · simp [frameTagTabled] at ht
  · simp [frameTagTabled] at ht

end CFSG.StandardType.FrameRoute

end
