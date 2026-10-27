module

public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTBRowR5U (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .twA ∧ 3 ≤ lab.rank ∧ ¬ p ∣ lab.rank + 1) ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
    p ∣ 2 ^ lab.n + 1

@[expose] def GGTBRowR5Ud (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGTBRowR5O1 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ 4 ≤ lab.rank ∧ (p ∣ 2 ^ lab.n - 1 ∨ (Even lab.rank ∧ p ∣ 2 ^ lab.n + 1))

@[expose] def GGTBRowR5O2 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ 4 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGTBRowR5V (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGTBRowR5Par (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTBRowR5 p lab ∧ ((lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .twD ∧ (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1)))

theorem ggTBRowR5Par_cases {p : ℕ} {lab : LargeEvenLabel} (h : GGTBRowR5Par p lab) :
    GGTBRowR5U p lab ∨ GGTBRowR5Ud p lab ∨ GGTBRowR5O1 p lab ∨ GGTBRowR5O2 p lab ∨
      GGTBRowR5V p lab := by
  obtain ⟨⟨-, h3⟩, hpar⟩ := h
  rcases hpar with ⟨hA, hdA⟩ | ⟨hD, hdD⟩
  · by_cases hd : p ∣ lab.rank + 1
    · exact Or.inr (Or.inl ⟨hA, h3, hd, hdA⟩)
    · exact Or.inl ⟨Or.inl ⟨hA, h3, hd⟩, hdA⟩
  · by_cases h3' : lab.rank = 3
    · rcases hdD with hp | hm
      · exact Or.inl ⟨Or.inr ⟨hD, h3'⟩, hp⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hD, h3', hm⟩)))
    · have h4 : 4 ≤ lab.rank := by omega
      rcases hdD with hp | hm
      · rcases Nat.even_or_odd lab.rank with he | ho
        · exact Or.inr (Or.inr (Or.inl ⟨hD, h4, Or.inr ⟨he, hp⟩⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hD, h4, ho, hp⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨hD, h4, Or.inl hm⟩))

end CFSG.StandardType

end
