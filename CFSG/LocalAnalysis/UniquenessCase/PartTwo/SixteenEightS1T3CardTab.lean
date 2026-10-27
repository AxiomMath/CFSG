module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3CardTabSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3CardTabOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3CardTabAlt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16t3_small_shape_valuations {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X)
    (hX : ∃ n : ℕ, (IsSLn X n 1 ∧ n < 8) ∨ (IsSpn X n 1 ∧ n < 8) ∨ (IsOmegaPlus X n 1 ∧ n < 8) ∨
      (IsOmegaMinus X n 1 ∧ n < 10) ∨ (UC22.IsAlt X n ∧ n < 12)) :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ^ 3 ∣ Nat.card X) ∧
      (7 ^ 2 ∣ Nat.card X → IsSLn X 6 1 ∨ IsSLn X 7 1) := by
  obtain ⟨n, hn | hn | hn | hn | hn⟩ := hX
  · exact s16t3_val_card_sl hq hn.1 hn.2
  · obtain ⟨h1, h2⟩ := s16t3_val_card_om hq ⟨n, Or.inl hn⟩
    exact ⟨h1, fun h => absurd h h2⟩
  · obtain ⟨h1, h2⟩ := s16t3_val_card_om hq ⟨n, Or.inr (Or.inl hn)⟩
    exact ⟨h1, fun h => absurd h h2⟩
  · obtain ⟨h1, h2⟩ := s16t3_val_card_om hq ⟨n, Or.inr (Or.inr hn)⟩
    exact ⟨h1, fun h => absurd h h2⟩
  · obtain ⟨h1, h2⟩ := s16t3_val_card_alt hq hn.1 hn.2
    exact ⟨h1, fun h => absurd h h2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
