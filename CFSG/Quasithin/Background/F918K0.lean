module

public import CFSG.Open.Defs

public section

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def NSCard (N : ℕ) : Prop :=
  N = 175560 ∨ ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ N = ordA 1 p

structure NSGroup (X : Type) [Group X] : Prop where
  isSimple : IsSimpleGroup X
  noncomm : ∃ a b : X, a * b ≠ b * a
  card : NSCard (Nat.card X)
  rank : ∀ E : Subgroup X, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 2 = 1) →
    Nat.card E ≤ 8

end CFSG.Quasithin
