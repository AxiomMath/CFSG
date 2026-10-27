module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def IsU45 (X : Type) [Group X] (n : ℕ) : Prop :=
  (IsU5 X n ∧ n = 2) ∨ (IsU4 X n ∧ Even n)

@[expose] def KU4OddRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU4 X n → Odd n →
    3 ≤ Open.pRank 3 (⊤ : Subgroup X)

@[expose] def KU45Syl3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU45 X n →
    ∀ S : Subgroup X, IsPGroup 3 S → ¬ 3 ∣ S.index →
      (∃ E : Subgroup X, E ≤ S ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
          ∀ s ∈ S, s ^ 3 = 1 → s ∈ E) ∧
        ∀ α : MulAut X, (∃ k : ℕ, α ^ (3 ^ k) = 1) → (∀ s ∈ S, α s ∈ S) →
          ∀ s ∈ S, s ^ 3 = 1 → α s = s

@[expose] def KU45Key : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU45 X n →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ∣ 2 ^ n + 1 →
      ∀ R : Subgroup (MulAut X), IsElemAbelian p R →
        ∃ S : Subgroup X, IsPGroup 3 S ∧ ¬ 3 ∣ S.index ∧
          ∃ C : Subgroup (MulAut X), C ≤ R ∧ (∀ α ∈ C, ∀ s ∈ S, α s = s) ∧
            Nat.card R ≤ p * Nat.card C

@[expose] def KU4SylOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU4 X n → Even n →
    ∀ q p : ℕ, q.Prime → p.Prime → q ∣ 2 ^ n + 1 → p ∣ 2 ^ n + 1 →
      ∀ S : Subgroup X, IsPGroup q S → ¬ q ∣ S.index →
        (∃ E : Subgroup X, E ≤ S ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
            2 ≤ Open.pRank p (centralizer (E : Set X))) ∧
          ∀ α : MulAut X, (∃ k : ℕ, α ^ (q ^ k) = 1) → (∀ s ∈ S, α s ∈ S) →
            ∀ s ∈ S, s ^ q = 1 → α s = s

@[expose] def KU45Types : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU45 X n →
    ∀ p : ℕ, p.Prime → p ∣ 2 ^ n + 1 → ∀ S : Subgroup X, IsPGroup 3 S → ¬ 3 ∣ S.index →
      (∃ A : Subgroup X, F08.NotationA8103 ⊤ S p n A) ∧
      (∃ B : Subgroup X, F08.NotationB8103 ⊤ S n B) ∧
      (∀ Y : Subgroup X, Y ≤ S → Nat.card Y = 3 →
        F08.NotationA8103 ⊤ S p n Y ∨ F08.NotationB8103 ⊤ S n Y) ∧
      (∀ A : Subgroup X, F08.NotationA8103 ⊤ S p n A →
        p ∣ Nat.card (Bar2 (F08.DerInf8 (⊤ ⊓ centralizer (A : Set X))))) ∧
      ∀ B₁ B₂ : Subgroup X, F08.NotationB8103 ⊤ S n B₁ → F08.NotationB8103 ⊤ S n B₂ →
        ∃ x : X, B₂ = B₁.map (MulAut.conj x).toMonoidHom

@[expose] def KU45Out : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU45 X n →
    ∀ α : MulAut X, α ∈ commutator (MulAut X) → (∃ k : ℕ, α ^ (3 ^ k) = 1) →
      α ∈ (MulAut.conj : X →* MulAut X).range

@[expose] def KU45TorusFix : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU45 X n →
    ∀ S : Subgroup X, IsPGroup 3 S → ¬ 3 ∣ S.index →
      ∀ Θ : Subgroup (MulAut X), IsPGroup 3 Θ → (∀ α ∈ Θ, ∀ s ∈ S, α s ∈ S) →
        ∃ q : ℕ, q.Prime ∧ q ∣ 2 ^ n + 1 ∧ ∃ x : X, orderOf x = q ∧
          (∀ s ∈ S, x * s = s * x) ∧ ∀ α ∈ Θ, α x = x

@[expose] def KAltTen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Λ : Subgroup X), Λ.Normal → genFittingFStar X ≤ Λ →
    IsAlt Λ 10 → ∀ E : Subgroup X, IsElemAbelian 5 E → Nat.card E = 25 →
      ∃ U₁ U₂ : Subgroup X, U₁ ≤ E ∧ U₂ ≤ E ∧ Nat.card U₁ = 5 ∧ Nat.card U₂ = 5 ∧ U₁ ≠ U₂ ∧
        5 ∣ Nat.card (F08.DerInf8 (centralizer (U₁ : Set X))) ∧
        5 ∣ Nat.card (F08.DerInf8 (centralizer (U₂ : Set X)))

@[expose] def KU45AltFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU45 X n → ∀ A : Subgroup X, Nat.card A = 3 →
    IsAlt (Bar2 (F08.DerInf8 (⊤ ⊓ centralizer (A : Set X)))) 5 →
      (∀ U₁ U₂ : Subgroup X,
        U₁ ≤ centralizer (A : Set X) ⊓
          centralizer (F08.DerInf8 (⊤ ⊓ centralizer (A : Set X)) : Set X) →
        U₂ ≤ centralizer (A : Set X) ⊓
          centralizer (F08.DerInf8 (⊤ ⊓ centralizer (A : Set X)) : Set X) →
        Nat.card U₁ = 5 → Nat.card U₂ = 5 → U₁ = U₂) ∧
      (∀ u ∈ centralizer (A : Set X), orderOf u = 5 →
        u ∉ centralizer (F08.DerInf8 (⊤ ⊓ centralizer (A : Set X)) : Set X) →
        ∀ Y : Subgroup (MulAut X), ⁅Y, Y⁆ = Y → (∀ α ∈ Y, ∀ a ∈ A, α a = a) →
          (∀ α ∈ Y, α u = u) → Y = ⊥) ∧
      3 ≤ Open.pRank 5 (⊤ : Subgroup X)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
