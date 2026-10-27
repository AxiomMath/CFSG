module

public import CFSG.RankThree.GF2n.Smith81.Bridge
public import CFSG.RankThree.GF2n.Smith81.LinSetup
public import CFSG.RankThree.GF2n.Smith81.Sec1Fusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Lin212CondProp (M Q Z B : Subgroup G) (V₁ V₂ : Subgroup G) : Prop :=
  ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → Q ⊓ QB X ≠ ⊥ →
    x ∈ Lgen M (LB M Q B) ∧ HasDimOn V₁ Z 1 x ∧ HasDimOn V₂ Z 1 x ∧
    (∀ z' ∈ Z, InZClass Z (x * z') → z' = 1) ∧
    (∀ g q : G, q ∈ Q → g * x * g⁻¹ = x * q → ∃ q' ∈ Q, g * x * g⁻¹ = q' * x * q'⁻¹)

@[expose] def Lin212CondStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n →
      Lin212CondProp M Q Z B V₁ V₂

@[expose] def LinSwapStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n → ∀ t ∈ H0 M Z,
      (conjSubgroup t V₁ = V₁ ∧ conjSubgroup t V₂ = V₂) ∨
      (conjSubgroup t V₁ = V₂ ∧ conjSubgroup t V₂ = V₁)

@[expose] def LinNonswapStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n → ∀ t ∈ H0 M Z, t * t ∈ Q →
      conjSubgroup t V₁ = V₁ → t ∈ Lgen M (LB M Q B)

@[expose] def LinRankBoundStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → ∀ a ∈ Lgen M (LB M Q B), a ∉ Q → a * a ∈ Q →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ n / 2 ∧ HasDimOn V₁ Z k a ∧ HasDimOn V₂ Z k a

@[expose] def LinGammaStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B X : Subgroup G) (x : G) (n m : ℕ)
    (V₁ V₂ : Subgroup G), Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → n = 2 * m + 1 → 1 ≤ m →
    (∀ v ∈ V₁, v * v = 1) → (∀ v ∈ V₂, v * v = 1) → Sit M Q Z X x →
    x ∈ Lgen M (LB M Q B) → Q ⊓ QB X = ⊥ →
      Nat.card ↥(Kx Q X) = Nat.card Z ^ (n + 1) ∧
      (∀ z ∈ Z, ∃ c ∈ Q, c * x * c⁻¹ = x * z) ∧
      ∃ V ∈ ({V₁, V₂} : Set (Subgroup G)),
        Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card Z ^ (m + 2) ∧
        ⁅V, Subgroup.zpowers x⁆ ⊓ Z = ⊥ ∧
        Nat.card ↥⁅V, Subgroup.zpowers x⁆ = Nat.card Z ^ m

@[expose] def LinGammaEvenStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B X : Subgroup G) (x : G) (n m : ℕ)
    (V₁ V₂ : Subgroup G), Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → n = 2 * m → 2 ≤ m →
    (∀ v ∈ V₁, v * v = 1) → (∀ v ∈ V₂, v * v = 1) → Sit M Q Z X x →
    x ∈ Lgen M (LB M Q B) → Q ⊓ QB X = ⊥ →
      Nat.card ↥(Kx Q X) = Nat.card Z ^ (n + 1) ∧
      ∀ V ∈ ({V₁, V₂} : Set (Subgroup G)),
        Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card Z ^ (m + 1) ∧
        ⁅V, Subgroup.zpowers x⁆ ⊓ Z = ⊥ ∧ Nat.card ↥⁅V, Subgroup.zpowers x⁆ = Nat.card Z ^ m

@[expose] def LinFourCountStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B Y : Subgroup G) (y : G) (V₁ V₂ : Subgroup G),
    Ctx M Q Z B → LinSetup M Q Z B 4 V₁ V₂ → (∀ v ∈ V₁, v * v = 1) → (∀ v ∈ V₂, v * v = 1) →
    Sit M Q Z Y y → y ∈ Lgen M (LB M Q B) → Q ⊓ QB Y = ⊥ →
      Nat.card ↥(Lx M Y) ≤ Nat.card Z ^ 4

@[expose] def Lin212C4Prop (M Q Z : Subgroup G) : Prop :=
  ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → Q ⊓ QB X ≠ ⊥ →
    ∀ z' ∈ Z, InZClass Z (x * z') → z' = 1

@[expose] def Lin212C7Prop (M Q Z : Subgroup G) : Prop :=
  ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → Q ⊓ QB X ≠ ⊥ →
    ∀ g q : G, q ∈ Q → g * x * g⁻¹ = x * q → ∃ q' ∈ Q, g * x * g⁻¹ = q' * x * q'⁻¹

@[expose] def Lin212C7Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n →
      Lin212C7Prop M Q Z

theorem Lin212CondProp.c4 {M Q Z B V₁ V₂ : Subgroup G} (h : Lin212CondProp M Q Z B V₁ V₂) :
    Lin212C4Prop M Q Z := fun X x hs hne => (h X x hs hne).2.2.2.1

end CFSG.RankThree.GF2n.Smith81
