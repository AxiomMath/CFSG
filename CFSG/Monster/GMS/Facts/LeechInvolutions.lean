module

public import CFSG.Monster.GMS.Facts.Leech

public section

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

@[expose] def LeechInvolutionData (z : G) : Prop :=
  (∀ r₀ ∈ Subgroup.centralizer ({z} : Set G), orderOf r₀ = 2 → r₀ ∉ leechQ z →
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {r₀}) =
      2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 →
    ∀ x ∈ Subgroup.centralizer ({z} : Set G), orderOf x = 2 → x ∉ leechQ z →
      ∃ g ∈ Subgroup.centralizer ({z} : Set G), ∀ k : ℕ, orderOf (g * r₀ * g⁻¹ * x) ≠ 2 ^ k) ∧
  (∀ r ∈ Subgroup.centralizer ({z} : Set G), ∀ r' ∈ Subgroup.centralizer ({z} : Set G),
    orderOf r = 2 → orderOf r' = 2 → r ∉ leechQ z → r' ∉ leechQ z →
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {r}) =
      2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 →
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {r'}) =
      2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 →
      ∃ g ∈ Subgroup.centralizer ({z} : Set G), g * r' * g⁻¹ = r ∨ g * r' * g⁻¹ = r * z)

@[expose] def LeechInvolutionStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), GMSLeechCentralizer z → LeechInvolutionData z

end CFSG.Monster.GMS
