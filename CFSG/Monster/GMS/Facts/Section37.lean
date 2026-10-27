module

public import CFSG.Monster.GMS.Facts.Section36

public section

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

@[expose] def LineOddOrder (a : G) : Prop :=
  ∀ y z : G, IsConj a y → z ∈ twoANbr a y →
    ∀ M : Subgroup G, M ≤ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer {z} →
      Odd (Nat.card M) → Nat.card M ≤ 54463 ∧
        (Nat.card M ∣ 3 ^ 6 * 5 ^ 2 * 7 * 11 * 19 → Nat.card M ≤ 9477) ∧
        (Nat.card M ∣ 3 ^ 7 * 5 ^ 2 * 7 * 11 * 19 → Nat.card M ≤ 15309)

@[expose] def FourAOddOrder (a z₀ : G) : Prop :=
  ∀ b y z : G, IsConj a b → y ∈ twoANbr a b → z ∈ tableVIOrbit a z₀ b y .four_A →
    ∀ M : Subgroup G,
      M ≤ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {y} ⊓ Subgroup.centralizer {z} →
        Odd (Nat.card M) → Nat.card M < 3000

@[expose] def EightOneOddOrder (a z₀ : G) : Prop :=
  ∀ x y t : G, IsLineTriple a x y → IsEightExt x y t → twoBCount z₀ x y t = 1 →
    ∀ M : Subgroup G,
      M ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ⊓ Subgroup.centralizer {t} →
        Odd (Nat.card M) → Nat.card M < 3000

@[expose] def EdgeSquares (a : G) : Prop :=
  ∀ b w : G, IsConj a b → w ∈ twoANbr a b →
    ∀ g ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {w},
      g * g ∈ ({1, b, w, b * w} : Set G) → g * g = 1

@[expose] def eightCentOrder : ℕ → ℕ
  | 1 => 2 ^ 38 * 3 ^ 6 * 5 * 7 * 11
  | 3 => 2 ^ 35 * 3 ^ 4 * 5 * 7
  | 4 => 2 ^ 31 * 3 ^ 3
  | _ => 0

@[expose] def EightCentOrders (a z₀ : G) : Prop :=
  ∀ x y t : G, IsLineTriple a x y → IsEightExt x y t →
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ⊓
      Subgroup.centralizer {t}) = eightCentOrder (twoBCount z₀ x y t)

@[expose] def CommonNbrTwoB (a z₀ : G) : Prop :=
  ∀ x y t : G, IsConj a x → t ∈ twoANbr a x → y ∈ twoANbr a t → orderOf (x * y) = 3 →
    ∃ w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}, IsConj z₀ w

end CFSG.Monster.GMS
