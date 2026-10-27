module

public import CFSG.Permutation.BurnsideSchur.Main

public section

universe u v w

namespace CFSG

open MulAction BurnsideSchur in
theorem _root_.CFSG.Milestones.burnside_schur {Ω : Type*} [Finite Ω] (G K : Subgroup (Equiv.Perm Ω))
    (hΩ : 2 ≤ Nat.card Ω) (hKG : K ≤ G) [IsPreprimitive G Ω] [IsCyclic K]
    [IsPretransitive K Ω] (hK : ∀ x : Ω, stabilizer K x = ⊥) :
    IsMultiplyPretransitive G Ω 2 ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card Ω = p ∧ ∃ e : Ω ≃ ZMod p,
        e.permCongr '' (K : Set (Equiv.Perm Ω)) = {t | ∃ b, ∀ x, t x = x + b} ∧
        (∀ g ∈ G, ∃ a ≠ 0, ∃ b, ∀ x, e (g x) = a * e x + b) ∧
        (K.subgroupOf G).Normal :=
  _root_.CFSG.burnside_schur G K hΩ hKG hK

end CFSG
