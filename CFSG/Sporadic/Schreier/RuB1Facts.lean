module

public import CFSG.Sporadic.Schreier.RuDefs

public section

namespace CFSG.Sporadic.RuSchreier

open Subgroup

structure RuB1NativeFacts (A₁ X : Subgroup (Equiv.Perm (Fin 4060)))
    (g₅ : Equiv.Perm (Fin 4060)) : Prop where
  A1_char : ∀ E : Subgroup (Equiv.Perm (Fin 4060)), E ≤ ruS → ruZ ∈ E → Nat.card E = 8 →
    (∀ x ∈ E, x * x = 1) → Nat.card ↥(ruS ⊓ centralizer (E : Set (Equiv.Perm (Fin 4060)))) = 2048 →
    E = A₁
  X_eq : X = closure {x | ∃ c ∈ ruC, ∃ a ∈ A₁, x = c * a * c⁻¹}
  X_comm : ∀ x ∈ X, ∀ x' ∈ X, x * x' = x' * x
  X_sq : ∀ x ∈ X, x * x = 1
  card_X : Nat.card X = 32
  X_le : X ≤ ruS
  g5_mem : g₅ ∈ ruC
  g5_order : orderOf g₅ = 5
  g5_cent : ∀ x ∈ X, g₅ * x = x * g₅ → x = 1 ∨ x = ruZ
  g5_gen : ∀ u ∈ X, u ≠ 1 → u ≠ ruZ → X ≤ closure (insert ruZ
    (Set.range fun i : Fin 5 => g₅ ^ (i : ℕ) * u * (g₅ ^ (i : ℕ))⁻¹))
  F8 : ∀ y ∈ ruS, y * y = 1 → y ∉ centralizer (A₁ : Set (Equiv.Perm (Fin 4060))) →
    ∃ l ∈ ruP, A₁.map (MulAut.conj l).toMonoidHom ≤
      ruS ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 4060)))

end CFSG.Sporadic.RuSchreier
