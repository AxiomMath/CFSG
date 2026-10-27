module

public import CFSG.Monster.GMS.Facts.Leech

public section

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

@[expose] def IsLeechTwo (z q : G) : Prop :=
  q ∈ leechQ z ∧ q ≠ 1 ∧ q ≠ z ∧ q * q = 1 ∧
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {q}) =
      2 ^ 42 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23

@[expose] def LeechPairData (z : G) : Prop :=
  (∀ q₁ q₂ q₁' q₂' : G, IsLeechTwo z q₁ → IsLeechTwo z q₂ → IsLeechTwo z q₁' →
    IsLeechTwo z q₂' → (q₁ * q₂) * (q₁ * q₂) = z → (q₁' * q₂') * (q₁' * q₂') = z →
      ∃ g ∈ Subgroup.centralizer ({z} : Set G), g * q₁ * g⁻¹ = q₁' ∧ g * q₂ * g⁻¹ = q₂') ∧
  (∀ q₁ q₂ : G, IsLeechTwo z q₁ → IsLeechTwo z q₂ → (q₁ * q₂) * (q₁ * q₂) = z →
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {q₁} ⊓
      Subgroup.centralizer {q₂}) = 2 ^ 30 * 3 ^ 6 * 5 ^ 3 * 7 * 11) ∧
  (∀ q₁ q₂ q₃ : G, IsLeechTwo z q₁ → IsLeechTwo z q₂ → IsLeechTwo z q₃ →
    (q₁ * q₂) * (q₁ * q₂) = z → IsLeechTwo z (q₁ * q₃) → IsLeechTwo z (q₃ * q₂) →
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {q₁} ⊓
      Subgroup.centralizer {q₃} ⊓ Subgroup.centralizer {q₂}) = 2 ^ 29 * 3 ^ 6 * 5 * 7)

@[expose] def LeechPairStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), GMSLeechCentralizer z → LeechPairData z

end CFSG.Monster.GMS
