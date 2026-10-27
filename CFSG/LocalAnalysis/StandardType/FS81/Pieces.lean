module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

@[expose] def L0CanonPosition : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (m : ℕ),
    HypSetup b₀ K E m → ∃ r : Row, m = r.m ∧ CanonPosition b₀ K E r

@[expose] def L1Local : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (r : Row),
    StdAssumptions b₀ K E r →
      ∃ B : Basis3 G (r.n + 1), Adapted B b₀ K E ∧ LocalData r B b₀

@[expose] def L1Fus42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (r : Row),
    StdAssumptions b₀ K E r → ∀ B : Basis3 G (r.n + 1), Adapted B b₀ K E → LocalData r B b₀ →
      Fus42 B b₀

@[expose] def L1OddCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (r : Row),
    StdAssumptions b₀ K E r → ∀ B : Basis3 G (r.n + 1), Adapted B b₀ K E → LocalData r B b₀ →
      Fus42 B b₀ → OddCoreTrivial E

@[expose] def L1NotMonomial : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (r : Row),
    r ≠ Row.E7 → StdAssumptions b₀ K E r → ∀ B : Basis3 G (r.n + 1), Adapted B b₀ K E →
      Fus42 B b₀ → OddCoreTrivial E → LocalOrthI B b₀ → False

@[expose] def L1N6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.D6 → ∀ B : Basis3 G (Row.D6.n + 1), Adapted B b₀ K E →
      LocalOrthII B b₀ → Fus42 B b₀ → OddCoreTrivial E →
        ∃ B' : Basis3 G (Row.D6.n + 1), Adapted B' b₀ K E ∧ RecOut Row.D6 B' b₀

@[expose] def L1N7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G)
    (K E : Subgroup G), StdAssumptions b₀ K E Row.twD7 →
      ∀ B : Basis3 G (Row.twD7.n + 1), Adapted B b₀ K E →
        LocalOrthII B b₀ → Fus42 B b₀ → OddCoreTrivial E →
          ∃ B' : Basis3 G (Row.twD7.n + 1), Adapted B' b₀ K E ∧ RecOut Row.twD7 B' b₀

@[expose] def L1E7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.E7 → ∀ B : Basis3 G (Row.E7.n + 1), Adapted B b₀ K E →
      LocalE7 B b₀ → Fus42 B b₀ → OddCoreTrivial E →
        ∃ B' : Basis3 G (Row.E7.n + 1), Adapted B' b₀ K E ∧ RecOut Row.E7 B' b₀

@[expose] def L2ConstructY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (r : Row),
    StdAssumptions b₀ K E r → ∀ B : Basis3 G (r.n + 1), Adapted B b₀ K E → RecOut r B b₀ →
      ∃ Y : Subgroup G, IsEm r.m Y ∧
        Subgroup.centralizer ({b₀} : Set G) ⊓ Y = Subgroup.zpowers b₀ ⊔ K ∧
        ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
          (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
          R ≤ Subgroup.centralizer (Y : Set G)

@[expose] def L3RootFusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (r : Row),
    StdAssumptions b₀ K E r → IsCharTwoType G →
      ∀ B : Basis3 G (r.n + 1), Adapted B b₀ K E → RecOut r B b₀ → Fus42 B b₀ →
      ∀ Y : Subgroup G, IsEm r.m Y →
        Subgroup.centralizer ({b₀} : Set G) ⊓ Y = Subgroup.zpowers b₀ ⊔ K →
        (∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
          (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
          R ≤ Subgroup.centralizer (Y : Set G)) →
        ∃ (S : Subgroup G) (t : G), IsSylow2In S Y ∧ t ∈ S ∧ orderOf t = 2 ∧
          (∀ s ∈ S, s * t = t * s) ∧ ∀ g : G, g * t * g⁻¹ ∈ Y → g ∈ Y

@[expose] def L3HoltEnd : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsCharTwoType G →
    ∀ (r : Row) (Y S : Subgroup G) (t : G), IsEm r.m Y → Y ≠ ⊤ → IsSylow2In S Y → t ∈ S →
      orderOf t = 2 → (∀ s ∈ S, s * t = t * s) → (∀ g : G, g * t * g⁻¹ ∈ Y → g ∈ Y) → False

end CFSG.StandardType.FrameRoute.FS81
