module

public import CFSG.Monster.GMS.Facts.Leech

public section

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

@[expose] def LeechCosetData (z : G) : Prop :=
  ∀ t ∈ Subgroup.centralizer ({z} : Set G), orderOf t = 2 → t ∉ leechQ z →
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t}) =
      2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 →
    ∀ g ∈ Subgroup.centralizer ({z} : Set G), t⁻¹ * (g * t * g⁻¹) ∈ leechQ z →
      ∃ q ∈ leechQ z, q * t * q⁻¹ = g * t * g⁻¹ ∨ q * (t * z) * q⁻¹ = g * t * g⁻¹

@[expose] def LeechCosetStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), GMSLeechCentralizer z → LeechCosetData z

end CFSG.Monster.GMS
