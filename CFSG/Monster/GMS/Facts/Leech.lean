module

public import CFSG.Monster.GMS.Defs

public section

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

@[expose] def leechQ (z : G) : Subgroup G :=
  (CFSG.pCore 2 (Subgroup.centralizer ({z} : Set G))).map
    (Subgroup.centralizer ({z} : Set G)).subtype

@[expose] def LeechData (z : G) : Prop :=
  ∃ T₂ T₃ T₄ : Set G,
    (∀ q ∈ leechQ z, q ≠ 1 → q ≠ z → q ∈ T₂ ∨ q ∈ T₃ ∨ q ∈ T₄) ∧
    T₂ ⊆ leechQ z ∧ T₃ ⊆ leechQ z ∧ T₄ ⊆ leechQ z ∧
    Disjoint T₂ T₃ ∧ Disjoint T₂ T₄ ∧ Disjoint T₃ T₄ ∧
    (∀ q ∈ T₂, q ≠ 1 ∧ q ≠ z ∧ q * q = 1 ∧ q * z ∈ T₂) ∧
    (∀ q ∈ T₄, q ≠ 1 ∧ q ≠ z ∧ q * q = 1 ∧ q * z ∈ T₄) ∧
    (∀ q ∈ T₃, q * q = z) ∧
    (∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ q ∈ T₂, g * q * g⁻¹ ∈ T₂) ∧
    (∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ q ∈ T₃, g * q * g⁻¹ ∈ T₃) ∧
    (∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ q ∈ T₄, g * q * g⁻¹ ∈ T₄) ∧
    (∀ q ∈ T₂, ∀ q' ∈ T₂, ∃ g ∈ Subgroup.centralizer ({z} : Set G), g * q * g⁻¹ = q') ∧
    (∀ q ∈ T₃, ∀ q' ∈ T₃, ∃ g ∈ Subgroup.centralizer ({z} : Set G), g * q * g⁻¹ = q') ∧
    (∀ q ∈ T₄, ∀ q' ∈ T₄, ∃ g ∈ Subgroup.centralizer ({z} : Set G), g * q * g⁻¹ = q') ∧
    T₂.ncard = 196560 ∧ T₃.ncard = 16773120 ∧ T₄.ncard = 16584750 ∧
    (∀ q ∈ T₂, ∃ q' ∈ T₂, q * q' ∈ T₂ ∧
      3 ^ 6 * 11 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {q} ⊓
        Subgroup.centralizer {q'})) ∧
    (∀ q ∈ T₂, ∃ q' ∈ T₄, q * q' ∈ T₂ ∧
      2 ^ 41 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {q} ⊓
        Subgroup.centralizer {q'})) ∧
    (∀ q ∈ T₂, ∃ q' ∈ T₄, q * q' ∈ T₄) ∧
    (∀ t ∈ Subgroup.centralizer ({z} : Set G), orderOf t = 2 → t ∉ leechQ z →
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t}) ≤
        2 ^ 46 * 3 ^ 5 * 5 ^ 2 * 7) ∧
    (∀ t ∈ Subgroup.centralizer ({z} : Set G), orderOf t = 2 → t ∉ leechQ z →
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t}) =
        2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 →
        Nat.card ↥(leechQ z ⊓ Subgroup.centralizer {t}) = 2 ^ 17)

@[expose] def LeechStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), GMSLeechCentralizer z → LeechData z

end CFSG.Monster.GMS
