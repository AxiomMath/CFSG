module

public import Certificates.Data.OmegaTypes

public section

namespace Certificates.OmegaTypes

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups Certificates.P43Twin
  Certificates.OmegaPk

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def InvC (n : ℕ) (x : P45) : Prop :=
  x ∈ QA45.originalSubgroup ∧ x * x = 1 ∧ x ≠ 1 ∧
    Nat.card ↥(QA45.originalSubgroup ⊓ Subgroup.centralizer ({x} : Set P45)) = n

@[expose] def KAs : Set P45 := {x | x ∈ kaList ()}

@[expose] def KBs : Set P45 := {x | x ∈ kbList (g0 ()) (kaList ())}

structure Facts : Prop where
  rowA : InvC 1152 (tA ())
  rowB : InvC 192 (tB ())
  c : ∀ a b : P45, InvC 1152 a → InvC 1152 b → a ≠ b → a * b = b * a → InvC 192 (b * a)
  d : ∀ u : P45, InvC 192 u → u * tA () = tA () * u →
    ((∀ k ∈ KAs, u * k * u⁻¹ ∈ KAs) ∧ (∀ k ∈ KBs, u * k * u⁻¹ ∈ KBs) ∧
        (∃ k ∈ KAs, k * u * k⁻¹ = u * tA ()) ∧ ∃ k ∈ KBs, k * u * k⁻¹ = u * tA ()) ∨
      ((∀ k ∈ KAs, u * k * u⁻¹ ∈ KBs) ∧ (∀ k ∈ KBs, u * k * u⁻¹ ∈ KAs) ∧ InvC 1152 (u * tA ()))
  e : ∀ u : P45, InvC 96 u → (∀ k ∈ KAs, u * k * u⁻¹ ∈ KBs) → (∀ k ∈ KBs, u * k * u⁻¹ ∈ KAs) →
    u * tA () = tA () * u ∧ InvC 1440 (u * tA ())
  f : ∀ s u : P45, InvC 96 s ∨ InvC 192 s → u ∈ QA45.originalSubgroup → u * u = 1 → u ≠ 1 →
    u ≠ s → (∀ g ∈ QP45.originalSubgroup, g * s = s * g → g ^ 405 = 1 → u * g = g * u) →
    InvC 1152 u ∨ InvC 1440 u

end Certificates.OmegaTypes

end
