module

public import CFSG.Timmesfeld.Bridge.Asc72Triangle

public section

namespace CFSG.Timmesfeld.Bridge

open scoped commutatorElement

@[expose] def zStar (G : Type*) [Group G] : Subgroup G :=
  (Subgroup.center (G ⧸ CFSG.pCore 2 G)).comap (QuotientGroup.mk' (CFSG.pCore 2 G))

instance zStar_normal (G : Type*) [Group G] : (zStar G).Normal := by
  unfold zStar
  infer_instance

instance OddTransp.solvableRadical_normal (G : Type*) [Group G] :
    (CFSG.solvableRadical G).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

@[expose] def conjClosure {G : Type*} [Group G] (X : Subgroup G) (y : G) : Subgroup G :=
  Subgroup.closure {w | ∃ g ∈ X, w = g * y * g⁻¹}

@[expose] def NoPerfectCentralExt (G : Type*) [Group G] (Q : Subgroup G) : Prop :=
  ∀ Q₀ : Subgroup G, Q₀.Normal → Q₀ ≤ Q → ⁅Q, (⊤ : Subgroup G)⁆ ≤ Q₀ →
    Q ⊓ commutator G ≤ Q₀

@[expose] def OddTranspSimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Asc72.Setup G D →
    (∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D) →
    CFSG.solvableRadical G = zStar G ∧ IsSimpleGroup (G ⧸ zStar G)

structure SecondKindStructure {G : Type*} [Group G] (a b c : G) : Prop where
  le : conjClosure (Subgroup.closure {a, b}) (a * c) ≤ Subgroup.closure {a, b, c}
  normal : ∀ g ∈ Subgroup.closure {a, b, c}, ∀ q ∈ conjClosure (Subgroup.closure {a, b}) (a * c),
    g * q * g⁻¹ ∈ conjClosure (Subgroup.closure {a, b}) (a * c)
  comm : ∀ p ∈ conjClosure (Subgroup.closure {a, b}) (a * c),
    ∀ q ∈ conjClosure (Subgroup.closure {a, b}) (a * c), Commute p q
  sq : ∀ q ∈ conjClosure (Subgroup.closure {a, b}) (a * c), q * q = 1
  max : ∀ P : Subgroup G, P ≤ Subgroup.closure {a, b, c} →
    (∀ g ∈ Subgroup.closure {a, b, c}, ∀ p ∈ P, g * p * g⁻¹ ∈ P) → IsPGroup 2 P →
    P ≤ conjClosure (Subgroup.closure {a, b}) (a * c)
  eq_sup : conjClosure (Subgroup.closure {a, b}) (a * c) =
    ⁅conjClosure (Subgroup.closure {a, b}) (a * c), Subgroup.zpowers a⁆ ⊔
      ⁅conjClosure (Subgroup.closure {a, b}) (a * c), Subgroup.zpowers b⁆
  le_centralizer : ⁅conjClosure (Subgroup.closure {a, b}) (a * c), Subgroup.zpowers b⁆ ≤
    Subgroup.centralizer {b}
  conj : ∃ x ∈ ⁅conjClosure (Subgroup.closure {a, b}) (a * c), Subgroup.zpowers b⁆,
    x * a * x⁻¹ = c

@[expose] def OddTranspSecondKind : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Asc72.IsOddTransp D →
    Connectivity.IsNormalSet D → ∀ a b c : G, Asc72.IsTriangle D a b c →
    orderOf (a * c * b) = 4 →
    (∀ x ∈ D, x ∈ Subgroup.closure {a, b} → Asc72.IsTriangle D a x c →
      ¬ Asc72.IsThirdKind a x c) →
    SecondKindStructure a b c

structure ThirdKindHyp (G : Type*) [Group G] (D : Set G) (S : Sylow 2 G) (a b c : G) (n : ℕ) :
    Prop where
  setup : Asc72.Setup G D
  tri : Asc72.IsTriangle D a b c
  odd : Odd n
  one_lt : 1 < n
  order : orderOf (a * c * b) = 2 * n
  a_mem : a ∈ S
  c_mem : c ∈ S
  z_mem : (a * c * b) ^ n ∈ S
  gen : Subgroup.closure (insert b (D ∩ (S : Set G))) = ⊤
  npc : NoPerfectCentralExt G (CFSG.pCore 2 G)

@[expose] def OddTranspThirdKind : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (S : Sylow 2 G) (a b c : G) (n : ℕ),
    ThirdKindHyp G D S a b c n →
    (∀ y ∈ CFSG.pCore 2 G, (Commute y a ∧ Commute y b ↔ y ∈ Subgroup.center G)) ∧
    ∀ d ∈ D ∩ (S : Set G), ∀ e ∈ D ∩ (S : Set G), ∀ f ∈ D, f * d⁻¹ ∈ CFSG.pCore 2 G →
      ∃! p : G × G, p.1 ∈ D ∧ p.2 ∈ CFSG.pCore 2 G ⊓ Subgroup.center G ∧ d * e * f = p.1 * p.2

@[expose] def OddTranspZStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Asc72.IsOddTransp D →
    Connectivity.IsNormalSet D → Subgroup.closure D = ⊤ →
    (∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D) → Connectivity.Disconnected D →
    CFSG.BenderSuzuki.IsBenderGroup (G ⧸ zStar G)

@[expose] def OddTranspBender : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Asc72.Setup G D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    (∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D) →
    Connectivity.Disconnected D → CFSG.BenderSuzuki.IsBenderGroup G

end CFSG.Timmesfeld.Bridge
