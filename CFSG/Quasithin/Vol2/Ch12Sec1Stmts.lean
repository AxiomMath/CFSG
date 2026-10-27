module

public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.BlueprintB2Defs
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.H13.StatementsVocab

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

structure Hyp121 (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : QuasithinUnique.quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  maximal : quasithinIsMaximalLocal T L
  faithful : quasithinIsFaithfulLocal T L
  rank : n = 4 ∨ n = 5
  iso : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
  le : V ≤ Subgroup.normalizer (L : Set G)
  reduced : IsPrimeReduced 2 (V.subgroupOf (Subgroup.normalizer (L : Set G)))
  aut : Nonempty (↥(autOn (Subgroup.normalizer (L : Set G)) V) ≃* MulAut (↥L ⧸ CFSG.pCore 2 ↥L))
  inf : V₁ ⊓ V₂ = ⊥
  sup : V₁ ⊔ V₂ = V
  norm₁ : L ≤ Subgroup.normalizer (V₁ : Set G)
  norm₂ : L ≤ Subgroup.normalizer (V₂ : Set G)
  nat₁ : ∃ _ : IsMulCommutative ↥V₁, BinaryNaturalSL (V := ↥V₁) (autOn L V₁) ⊤ ⊥ n 1
  nat₂ : ∃ _ : IsMulCommutative ↥V₂, BinaryNaturalSL (V := ↥V₂) (autOn L V₂) ⊤ ⊥ n 1
  dual : ¬ IsXSectionIso₂ L V₁ ⊥ V₂ ⊥

@[expose] def Setup121Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) →
      pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G)

section Form

variable {G : Type} [Group G]

@[expose] def IsDualPairing121 (L V₁ V₂ : Subgroup G) (β : G → G → ZMod 2) : Prop :=
  (∀ a ∈ V₁, ∀ b ∈ V₁, ∀ c ∈ V₂, β (a * b) c = β a c + β b c) ∧
    (∀ a ∈ V₁, ∀ c ∈ V₂, ∀ d ∈ V₂, β a (c * d) = β a c + β a d) ∧
    (∀ a ∈ V₁, a ≠ 1 → ∃ c ∈ V₂, β a c = 1) ∧ (∀ c ∈ V₂, c ≠ 1 → ∃ a ∈ V₁, β a c = 1) ∧
    ∀ l ∈ L, ∀ a ∈ V₁, ∀ c ∈ V₂, β (l * a * l⁻¹) (l * c * l⁻¹) = β a c

@[expose] def IsSingular121 (V₁ V₂ : Subgroup G) (β : G → G → ZMod 2) (v : G) : Prop :=
  ∃ a ∈ V₁, ∃ c ∈ V₂, v = a * c ∧ β a c = 0

@[expose] def IsNonsingular121 (V₁ V₂ : Subgroup G) (β : G → G → ZMod 2) (v : G) : Prop :=
  ∃ a ∈ V₁, ∃ c ∈ V₂, v = a * c ∧ β a c = 1

end Form

@[expose] def Lem1211 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) (β : G → G → ZMod 2),
    Hyp121 G T L V V₁ V₂ n → IsDualPairing121 L V₁ V₂ β →
    ∀ v ∈ V, IsNonsingular121 V₁ V₂ β v →
      Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lem1213 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → n = 5 → wClos V 0 T ≤ T ⊓ Subgroup.centralizer (V : Set G)

@[expose] def Lem1214 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → n = 4 → ∀ v : G,
      V₁ ⊓ Subgroup.centralizer ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) =
        Subgroup.zpowers v →
      IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G)) (Subgroup.centralizer ({v} : Set G))

@[expose] def Lem1215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n →
      (∀ v : G, V₁ ⊓ Subgroup.centralizer
          ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) = Subgroup.zpowers v →
        IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
          (Subgroup.centralizer ({v} : Set G))) ∧
      ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → ∀ g : G, g * v * g⁻¹ = w →
        ∃ m ∈ Subgroup.normalizer (L : Set G), m * v * m⁻¹ = w

@[expose] def Lem1216 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n →
      (∀ v : G, (v ∈ V₁ ∨ v ∈ V₂) → v ≠ 1 →
        ∀ x ∈ conjClosure V (Subgroup.centralizer ({v} : Set G)),
          ∀ y ∈ conjClosure V (Subgroup.centralizer ({v} : Set G)), x * y = y * x) ∧
      ∀ g : G, V₁ ⊓ CFSG.conjugate V g ≠ ⊥ → ⁅V, CFSG.conjugate V g⁆ = ⊥

@[expose] def Lem1217 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → wClos V 0 T ≤ T ⊓ Subgroup.centralizer (V : Set G)

@[expose] def Lem1218 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → wClos V 1 T ≤ T ⊓ Subgroup.centralizer (V : Set G)

@[expose] def Lem1219 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n →
      (∀ X : Subgroup G,
        X ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) → X ≠ ⊥ →
          Odd (Nat.card X) → Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
      (∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H → E1.nParam H = 2) ∧
      ((n + 2 : ℕ) : ℕ∞) ≤ rParam V

@[expose] def Lem12110 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → wClos V 2 T ≤ T ⊓ Subgroup.centralizer (V : Set G)

end CFSG.Quasithin.H13
