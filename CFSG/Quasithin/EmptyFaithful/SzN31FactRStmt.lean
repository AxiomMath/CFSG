module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.SzN31

@[expose] def FactRStmt : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Q : Type) [Group Q] [Finite Q], IsPGroup p Q →
    (∀ E : Subgroup Q, (∀ x ∈ E, x ^ p = 1) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      Nat.card E ≤ p ^ 2) →
    ∀ (Bh : Type) [Group Bh] [Finite Bh] (act : Bh →* MulAut Q),
      (∀ b : Bh, b * b = 1) → Nat.card Bh ≤ 4 * Nat.card act.ker

end CFSG.Quasithin.SzN31
