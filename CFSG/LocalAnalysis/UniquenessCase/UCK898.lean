module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def U3Range : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSU3 X n → 2 ≤ n

@[expose] def U3FixInner : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSU3 X n → ∀ s : ℕ, Odd s → s ∣ n →
    ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 → ∀ α : MulAut X, α ^ r = 1 →
      α ∈ (MulAut.conj : X →* MulAut X).range →
        ∀ q : ℕ, q.Prime → 3 < q → q ∣ 2 ^ n + 1 → ∃ z : X, orderOf z = q ∧ α z = z

@[expose] def U3FixField : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSU3 X n → ∀ s : ℕ, Odd s → s ∣ n →
    ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 → ∀ α : MulAut X, α ^ r = 1 →
      α ∉ (MulAut.conj : X →* MulAut X).range →
        ∃ m : ℕ, n = r * m ∧
          ∀ q : ℕ, q.Prime → 3 < q → q ∣ 2 ^ m + 1 → ∃ z : X, orderOf z = q ∧ α z = z

end CFSG.LocalAnalysis.UniquenessCase.UCK
