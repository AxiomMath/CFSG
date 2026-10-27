module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3OutTabA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3OutTabB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16t3_not_three_dvd_outer {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X)
    (hX : ∃ n : ℕ, (IsSLn X n 1 ∧ n < 8) ∨ (IsSpn X n 1 ∧ n < 8) ∨ (IsOmegaPlus X n 1 ∧ n < 8) ∨
      (IsOmegaMinus X n 1 ∧ n < 10) ∨ (UC22.IsAlt X n ∧ n < 12)) :
    ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  obtain ⟨n, hn | hn | hn | hn | hn⟩ := hX
  · exact s16t3_not_three_dvd_outer_b hq hn.1 hn.2
  · exact s16t3_not_three_dvd_outer_a hq ⟨n, Or.inl hn⟩
  · exact s16t3_not_three_dvd_outer_a hq ⟨n, Or.inr (Or.inl hn)⟩
  · exact s16t3_not_three_dvd_outer_a hq ⟨n, Or.inr (Or.inr (Or.inl hn))⟩
  · exact s16t3_not_three_dvd_outer_a hq ⟨n, Or.inr (Or.inr (Or.inr hn))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
