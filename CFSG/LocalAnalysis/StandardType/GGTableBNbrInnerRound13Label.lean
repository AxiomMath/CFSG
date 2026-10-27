module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRound12ExcRow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTableBNbrInnerRound13ExcRow (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n + 1) ∨
  (lab.tag = .E6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1) ∨
  (lab.tag = .twE6 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)) ∨
  ((lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1) ∧ lab.rank = 5 ∧
    p = 3)

@[expose] def GGTableBNbrInnerRound13ExcLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBNbrInnerRound12Label p lab ∧ GGTableBNbrInnerRound13ExcRow p lab

theorem GGTableBNbrInnerRound13ExcRow.round12 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTableBNbrInnerRound13ExcRow p lab) : GGTableBNbrInnerRound12ExcRow p lab := by
  rcases h with h | ⟨ht, hp3, hd⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨ht, Or.inl ⟨hp3, hd⟩⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end CFSG.StandardType

end
