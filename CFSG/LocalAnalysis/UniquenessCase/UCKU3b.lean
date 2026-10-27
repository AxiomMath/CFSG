module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def U3SylOmega : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSU3 X n →
    ∀ q : ℕ, q.Prime → 3 < q → q ∣ 2 ^ n + 1 →
      ∀ S : Subgroup X, IsPGroup q S → ¬ q ∣ S.index →
        ∃ E : Subgroup X, E ≤ S ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
          ∀ s ∈ S, s ^ q = 1 → s ∈ E

@[expose] def U3SylCount : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSU3 X n →
    ∀ q p : ℕ, q.Prime → 3 < q → q ∣ 2 ^ n + 1 → p.Prime → p ≠ 2 → p ∣ 2 ^ n + 1 →
      ¬ p ∣ Nat.card (Sylow q X)

@[expose] def U3RankOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSU3 X n →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ 2 ^ n + 1 →
      ∀ R : Subgroup (MulAut X), R ≤ (MulAut.conj : X →* MulAut X).range →
        IsElemAbelian p R → Nat.card R ≤ p

end CFSG.LocalAnalysis.UniquenessCase.UCK
