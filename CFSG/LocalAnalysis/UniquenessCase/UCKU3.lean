module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def U3Center : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSU3 X n → Nat.card (center X) ∣ 3

@[expose] def U3OutShape : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSU3 X n →
    ∃ (N : Subgroup (MulAut X)) (_ : N.Normal),
      (MulAut.conj : X →* MulAut X).range ≤ N ∧ IsCyclic (MulAut X ⧸ N) ∧
      (∀ φ ∈ N, φ ^ 3 ∈ (MulAut.conj : X →* MulAut X).range) ∧
      (Even n → N ≤ (MulAut.conj : X →* MulAut X).range)

@[expose] def U3Syl : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSU3 X n →
    ∀ q : ℕ, q.Prime → 3 < q → q ∣ 2 ^ n + 1 →
      ∀ S : Subgroup X, IsPGroup q S → ¬ q ∣ S.index →
        (∃ E : Subgroup X, E ≤ S ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2) ∧
        ∀ α : MulAut X, (∃ k : ℕ, α ^ (q ^ k) = 1) → (∀ s ∈ S, α s ∈ S) →
          ∀ s ∈ S, s ^ q = 1 → α s = s

@[expose] def U3Key : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSU3 X n →
    ∀ q p : ℕ, q.Prime → 3 < q → q ∣ 2 ^ n + 1 → p.Prime → p ≠ 2 → p ≠ q →
      ∀ R : Subgroup (MulAut X), IsElemAbelian p R →
        (R ≤ (MulAut.conj : X →* MulAut X).range ∨ p ∣ 2 ^ n + 1) →
        ∃ S : Subgroup X, IsPGroup q S ∧ ¬ q ∣ S.index ∧
          ∃ E : Subgroup X, E ≤ S ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
            ((∃ B : Subgroup X, IsElemAbelian p B ∧ Nat.card B = p ^ 2 ∧
                B ≤ centralizer (E : Set X)) ∨
              ∃ C : Subgroup (MulAut X), C ≤ R ∧ (∀ α ∈ C, ∀ e ∈ E, α e = e) ∧
                Nat.card R ≤ p * Nat.card C)

end CFSG.LocalAnalysis.UniquenessCase.UCK
