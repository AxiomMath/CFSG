module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Algebra.Field.Defs

public section

namespace CFSG.Walter.Ree

variable (K : Type*) [Field K]

@[expose] def ESigma (σ : K ≃+* K) : Set (K × K × K) :=
  {p | σ p.1 * p.1 ^ 2 - σ p.2.1 * p.2.1 ^ 2 = -1 ∧ σ p.1 * p.1 - σ p.2.1 * p.2.1 = p.2.2 ∧
    p.2.2 ^ 3 ≠ p.2.2}

variable {K} in
@[expose] def thompsonT (a : ℕ) (z y u : K) : K :=
  z * (u - 1) ^ a - (z - y + 1) * u ^ a - y * (u + 1) ^ a + (u ^ 2 - 1) ^ a

@[expose] def IsThompsonAut (σ : K ≃+* K) : Prop :=
  (∀ τ : K ≃+* K, ∃ k : ℕ, τ = σ ^ k) ∧
  ∃ a s : ℕ, Even a ∧ Odd s ∧ (∀ x : K, (σ x * x) ^ a = x ^ 2) ∧
    (∀ x : K, (σ x * x ^ 2) ^ s = x) ∧ ∀ p ∈ ESigma K σ, thompsonT a p.1 p.2.1 p.2.2 = 0

end CFSG.Walter.Ree
