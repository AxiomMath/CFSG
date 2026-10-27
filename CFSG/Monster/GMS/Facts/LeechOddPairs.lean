module

public import CFSG.Monster.GMS.Facts.Leech

public section

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

@[expose] def IsLeechCentralLift (z t : G) : Prop :=
  t ∈ Subgroup.centralizer ({z} : Set G) ∧ orderOf t = 2 ∧ t ∉ leechQ z ∧
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t}) =
      2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 ∧
    ∀ g ∈ Subgroup.centralizer ({z} : Set G), g * t * g⁻¹ ≠ t * z

@[expose] def leechTriple (z t y : G) : Subgroup G :=
  Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t} ⊓ Subgroup.centralizer {y}

@[expose] def LeechOddType (z t y : G) : Fin 3 → Prop
  | 0 => orderOf (t * y) = 3 ∧
      Nat.card ↥(leechQ z ⊓ Subgroup.centralizer {t} ⊓ Subgroup.centralizer {y}) = 2 ^ 11 ∧
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t} ⊓
        Subgroup.centralizer {y}) = 2 ^ 18 * 3 ^ 5 * 5
  | 1 => orderOf (t * y) = 3 ∧
      Nat.card ↥(leechQ z ⊓ Subgroup.centralizer {t} ⊓ Subgroup.centralizer {y}) = 2 ^ 9 ∧
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t} ⊓
        Subgroup.centralizer {y}) = 2 ^ 15 * 3 ^ 4 * 5 * 7
  | 2 => orderOf (t * y) = 5 ∧
      Nat.card ↥(leechQ z ⊓ Subgroup.centralizer {t} ⊓ Subgroup.centralizer {y}) = 2 ^ 9 ∧
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t} ⊓
        Subgroup.centralizer {y}) = 2 ^ 14 * 3 ^ 2 * 5 ^ 2

@[expose] def IsLeechFour (z w₀ : G) : Prop :=
  w₀ ∈ leechQ z ∧ w₀ ≠ 1 ∧ w₀ ≠ z ∧ w₀ * w₀ = 1 ∧
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {w₀}) =
      2 ^ 45 * 3 ^ 3 * 5 * 7 * 11 * 23

@[expose] def HasCommonLeechFour (z t y : G) : Prop :=
  ∃ w₀, IsLeechFour z w₀ ∧ w₀ ∈ Subgroup.centralizer {t} ∧ w₀ ∈ Subgroup.centralizer {y}

@[expose] def LeechOddPairData (z : G) : Prop :=
  ∀ t : G, IsLeechCentralLift z t →
    (∀ y, (∃ g ∈ Subgroup.centralizer ({z} : Set G), g * t * g⁻¹ = y) → y ≠ t →
      Odd (orderOf (t * y)) → HasCommonLeechFour z t y → ∃! k, LeechOddType z t y k) ∧
    (∀ k, ∃ y, (∃ g ∈ Subgroup.centralizer ({z} : Set G), g * t * g⁻¹ = y) ∧ y ≠ t ∧
      HasCommonLeechFour z t y ∧ LeechOddType z t y k) ∧
    (∀ k y y', (∃ g ∈ Subgroup.centralizer ({z} : Set G), g * t * g⁻¹ = y) →
      (∃ g ∈ Subgroup.centralizer ({z} : Set G), g * t * g⁻¹ = y') →
      HasCommonLeechFour z t y → HasCommonLeechFour z t y' →
      LeechOddType z t y k → LeechOddType z t y' k →
        ∃ g ∈ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t}, g * y * g⁻¹ = y') ∧
    (∀ k y, k ≠ 0 → (∃ g ∈ Subgroup.centralizer ({z} : Set G), g * t * g⁻¹ = y) →
      HasCommonLeechFour z t y → LeechOddType z t y k →
      ∀ S : Sylow 2 ↥(leechTriple z t y), ∀ s : ↥(leechTriple z t y),
        s ∈ (S : Subgroup ↥(leechTriple z t y)) →
        (∀ s' : ↥(leechTriple z t y), s' ∈ (S : Subgroup ↥(leechTriple z t y)) →
          s * s' = s' * s) →
          (s : G) = 1 ∨ (s : G) = z)

@[expose] def LeechFiveAGenData (z : G) : Prop :=
  ∀ t : G, IsLeechCentralLift z t →
    ∀ y, (∃ g ∈ Subgroup.centralizer ({z} : Set G), g * t * g⁻¹ = y) →
      HasCommonLeechFour z t y → LeechOddType z t y 2 →
      Subgroup.closure {x : G | x ∈ Subgroup.centralizer ({z} : Set G) ⊓
          Subgroup.centralizer {t} ⊓ Subgroup.centralizer {y} ∧ orderOf x = 2 ∧
          ¬ (x ∈ leechQ z ∧ Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓
            Subgroup.centralizer {x}) = 2 ^ 42 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23) ∧
          ¬ ∃ g ∈ Subgroup.centralizer ({z} : Set G), g * t * g⁻¹ = x} =
        Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t} ⊓
          Subgroup.centralizer {y}

@[expose] def LeechOddPairStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), GMSLeechCentralizer z → LeechOddPairData z

end CFSG.Monster.GMS
