module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46.K22p

@[expose] def commSub {M : Type} [Group M] (σ : MulAut M) : Subgroup M :=
  Subgroup.closure (Set.range fun x : M => x⁻¹ * σ x)

@[expose] def FixesSylow {M : Type} [Group M] (σ : MulAut M) (q : ℕ) : Prop :=
  ∃ Q : Sylow q M, ∀ x ∈ (Q : Subgroup M), σ x = x

structure IsMinInv {M : Type} [Group M] (σ : MulAut M) (N : Subgroup M) : Prop where
  normal : N.Normal
  invariant : ∀ x ∈ N, σ x ∈ N
  ne_bot : N ≠ ⊥
  minimal : ∀ N' : Subgroup M, N'.Normal → (∀ x ∈ N', σ x ∈ N') → N' ≤ N → N' = ⊥ ∨ N' = N

@[expose] def ChiefAb : Prop :=
  ∀ (q : ℕ), q.Prime → ∀ (M : Type) [Group M] [Finite M] (σ : MulAut M), commSub σ = ⊤ →
    ∀ N : Subgroup M, N.Normal → IsPGroup q N → ¬ q ∣ N.index → FixesSylow σ q → N = ⊥

@[expose] def ChiefNon : Prop :=
  SimpleThreePrimeIsSz → SzOrder3Aut → ∀ (p : ℕ) (M : Type) [Group M] [Finite M],
    CFSG.Open.IsKGroup M → ¬ 3 ∣ Nat.card M → ∀ σ : MulAut M, σ ^ 3 = 1 → commSub σ = ⊤ →
    (∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → FixesSylow σ q) →
    ∀ N : Subgroup M, IsMinInv σ N → ¬ IsMulCommutative ↥N → False

@[expose] def K22pAbs : Prop :=
  SimpleThreePrimeIsSz → SzOrder3Aut → ∀ (p : ℕ) (M : Type) [Group M] [Finite M],
    CFSG.Open.IsKGroup M → ¬ 3 ∣ Nat.card M → ∀ σ : MulAut M, σ ^ 3 = 1 →
    (∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → FixesSylow σ q) →
    ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(commSub σ) → q = 2 ∨ q = p

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46.K22p
