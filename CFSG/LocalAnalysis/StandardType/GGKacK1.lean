module

public import CFSG.LocalAnalysis.StandardType.GGKacTableCl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGKacGenericCl (lab : LargeEvenLabel) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) ∧
    (lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨
      lab.tag = .twD) ∧
    ¬ (lab.tag = .A ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n - 1) ∧
    ¬ (lab.tag = .twA ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1)

@[expose] def GGKacGenericClA (lab : LargeEvenLabel) (p : ℕ) : Prop :=
  GGKacGenericCl lab p ∧
    (lab.tag = .A ∨ lab.tag = .twA ∨ (lab.tag = .D ∧ lab.rank = 3) ∨
      (lab.tag = .twD ∧ lab.rank ≤ 3))

@[expose] def GGKacGenericClC (lab : LargeEvenLabel) (p : ℕ) : Prop :=
  GGKacGenericCl lab p ∧ (lab.tag = .B ∨ lab.tag = .C)

@[expose] def GGKacGenericClD (lab : LargeEvenLabel) (p : ℕ) : Prop :=
  GGKacGenericCl lab p ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank

theorem ggKacLambda2_D_rank {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .D) : 3 ≤ lab.rank := by
  have := hlab.2
  simp only [h] at this
  exact this

theorem ggKacLambda2_twD_rank {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twD) : 2 ≤ lab.rank := by
  have := hlab.2
  simp only [h] at this
  exact this

theorem ggKacGenericCl_lanes {lab : LargeEvenLabel} {p : ℕ} (hlab : LargeEvenInLambda2 lab)
    (hgen : GGKacGenericCl lab p) :
    GGKacGenericClA lab p ∨ GGKacGenericClC lab p ∨ GGKacGenericClD lab p := by
  rcases hgen.2.2.2.1 with h | h | h | h | h | h
  · exact Or.inl ⟨hgen, Or.inl h⟩
  · exact Or.inl ⟨hgen, Or.inr (Or.inl h)⟩
  · exact Or.inr (Or.inl ⟨hgen, Or.inl h⟩)
  · exact Or.inr (Or.inl ⟨hgen, Or.inr h⟩)
  · have hr := ggKacLambda2_D_rank hlab h
    by_cases h3 : lab.rank = 3
    · exact Or.inl ⟨hgen, Or.inr (Or.inr (Or.inl ⟨h, h3⟩))⟩
    · exact Or.inr (Or.inr ⟨hgen, Or.inl h, by omega⟩)
  · have hr := ggKacLambda2_twD_rank hlab h
    by_cases h4 : 4 ≤ lab.rank
    · exact Or.inr (Or.inr ⟨hgen, Or.inr h, h4⟩)
    · exact Or.inl ⟨hgen, Or.inr (Or.inr (Or.inr ⟨h, by omega⟩))⟩

theorem ggK0Main_cl_of_lanes (hA : GGK0Main GGKacGenericClA GGKacValidCl)
    (hC : GGK0Main GGKacGenericClC GGKacValidCl) (hD : GGK0Main GGKacGenericClD GGKacValidCl) :
    GGK0Main GGKacGenericCl GGKacValidCl := by
  intro p lab hlab hgen
  rcases ggKacGenericCl_lanes hlab hgen with h | h | h
  · exact hA p lab hlab h
  · exact hC p lab hlab h
  · exact hD p lab hlab h

theorem ggK0Schur_cl_of_lanes (hA : GGK0Schur GGKacGenericClA) (hC : GGK0Schur GGKacGenericClC)
    (hD : GGK0Schur GGKacGenericClD) : GGK0Schur GGKacGenericCl := by
  intro p lab hlab hgen
  rcases ggKacGenericCl_lanes hlab hgen with h | h | h
  · exact hA p lab hlab h
  · exact hC p lab hlab h
  · exact hD p lab hlab h

end CFSG.StandardType

end
