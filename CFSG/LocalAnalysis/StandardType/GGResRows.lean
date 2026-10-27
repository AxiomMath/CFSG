module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def ggRowTwoNode (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  (J.tag = .A ∧ p ∣ 2 ^ J.n - 1 ∧ p ∣ J.rank + 3 ∧ X = ⟨.A, J.rank + 2, J.n⟩) ∨
  (J.tag = .twA ∧ p ∣ 2 ^ J.n + 1 ∧ p ∣ J.rank + 3 ∧ X = ⟨.twA, J.rank + 2, J.n⟩) ∨
  (J = ⟨.D, 4, J.n⟩ ∧ p = 3 ∧ 3 ∣ 2 ^ J.n - 1 ∧ X = ⟨.E6, 0, J.n⟩) ∨
  (J = ⟨.D, 4, J.n⟩ ∧ p = 3 ∧ 3 ∣ 2 ^ J.n + 1 ∧ X = ⟨.twE6, 0, J.n⟩)

@[expose] def ggRowMaxRank (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  (J = ⟨.A, 8, J.n⟩ ∧ p = 3 ∧ 3 ∣ 2 ^ J.n - 1 ∧ X = ⟨.E8, 0, J.n⟩) ∨
  (J = ⟨.twA, 8, J.n⟩ ∧ p = 3 ∧ 3 ∣ 2 ^ J.n + 1 ∧ X = ⟨.E8, 0, J.n⟩)

@[expose] def ggRowTriality (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  (J.tag = .triD4 ∧ p = 3 ∧ X = ⟨.D, 4, 3 * J.n⟩) ∨ (J.tag = .G2 ∧ p = 3 ∧ X = ⟨.D, 4, J.n⟩)

@[expose] def ggRowTriD4TwE6 (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  J.tag = .triD4 ∧ p = 3 ∧ 3 ∣ 2 ^ J.n + 1 ∧ X = ⟨.twE6, 0, J.n⟩

@[expose] def ggRowSeven (p : ℕ) (_J X : LargeEvenLabel) : Prop :=
  p = 7 ∧ (X = ⟨.A, 8, 1⟩ ∨ X = ⟨.A, 11, 1⟩ ∨ X = ⟨.E6, 0, 1⟩ ∨ X = ⟨.twE6, 0, 1⟩ ∨
    X = ⟨.E8, 0, 1⟩)

@[expose] def ggRowTwA2 (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  J.tag = .twA ∧ J.rank = 2 ∧ p = 3 ∧ X.tag = .twE6 ∧ 3 * X.n = J.n

@[expose] def GGResRowAt {G : Type} [Group G] (R : ℕ → LargeEvenLabel → LargeEvenLabel → Prop)
    (p : ℕ) (J X : Subgroup G) : Prop :=
  ∃ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧
    GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ GGHasLabel labX (↥X ⧸ Subgroup.center ↥X) ∧
    R p labJ labX

@[expose] def ggRowNonLevi (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  ggRowTwoNode p J X ∨ ggRowMaxRank p J X ∨ ggRowTriality p J X ∨ ggRowTriD4TwE6 p J X ∨
    ggRowSeven p J X ∨ ggRowTwA2 p J X

theorem GGResRowAt.cases {G : Type} [Group G] {p : ℕ} {J X : Subgroup G}
    (h : GGResRowAt ggRowNonLevi p J X) :
    GGResRowAt ggRowTwoNode p J X ∨ GGResRowAt ggRowMaxRank p J X ∨
      GGResRowAt ggRowTriality p J X ∨ GGResRowAt ggRowTriD4TwE6 p J X ∨
      GGResRowAt ggRowSeven p J X ∨ GGResRowAt ggRowTwA2 p J X := by
  obtain ⟨a, c, ha, hc, hJ, hX, hr | hr | hr | hr | hr | hr⟩ := h
  exacts [Or.inl ⟨a, c, ha, hc, hJ, hX, hr⟩, Or.inr (Or.inl ⟨a, c, ha, hc, hJ, hX, hr⟩),
    Or.inr (Or.inr (Or.inl ⟨a, c, ha, hc, hJ, hX, hr⟩)),
    Or.inr (Or.inr (Or.inr (Or.inl ⟨a, c, ha, hc, hJ, hX, hr⟩))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, c, ha, hc, hJ, hX, hr⟩)))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, c, ha, hc, hJ, hX, hr⟩))))]

end CFSG.StandardType
