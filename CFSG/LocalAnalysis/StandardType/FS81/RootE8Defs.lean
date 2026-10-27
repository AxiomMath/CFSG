module

public import CFSG.LocalAnalysis.StandardType.FS81.RowSplit

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

@[expose] def rowRootElt {G : Type} [Group G] : (r : Row) → Basis3 G (r.n + 1) → G → G
  | Row.D6, _, b₀ => b₀
  | Row.twD7, B, b₀ => b₀ * B.b 1
  | Row.E7, _, b₀ => b₀

@[expose] def s79A {G : Type} [Group G] : (r : Row) → Basis3 G (r.n + 1) → Subgroup G
  | Row.D6, _ => ⊥
  | Row.twD7, B => Subgroup.closure {B.b 2, B.b 3, B.b 4 * B.b 5}
  | Row.E7, B => Subgroup.closure {B.b 1 * B.b 2 * B.b 3, B.b 4 * B.b 5, B.b 6 * B.b 7}

structure RootSetting {G : Type} [Group G] [Finite G] (r : Row) (b₀ : G) (K E : Subgroup G)
    (B : Basis3 G (r.n + 1)) (Y : Subgroup G) : Prop where
  std : StdAssumptions b₀ K E r
  charTwo : IsCharTwoType G
  adapted : Adapted B b₀ K E
  recOut : RecOut r B b₀
  fus : Fus42 B b₀
  isEm : IsEm r.m Y
  cap : Subgroup.centralizer ({b₀} : Set G) ⊓ Y = Subgroup.zpowers b₀ ⊔ K
  core : ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
    R ≤ Subgroup.centralizer (Y : Set G)

@[expose] def RowCentAt (r : Row) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E r → ∀ B : Basis3 G (r.n + 1), Adapted B b₀ K E →
      RecOut r B b₀ → Fus42 B b₀ →
      ∃ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) ∧
        (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R ∧
        Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.zpowers b₀ ⊔ K)

@[expose] def E8RadicalAt (r : Row) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (B : Basis3 G (r.n + 1))
    (Y : Subgroup G), RootSetting r b₀ K E B Y →
    ∃ (t₀ : G) (L U : Subgroup G), orderOf t₀ = 2 ∧ L ≤ Y ∧
      L ≤ Subgroup.centralizer ({t₀} : Set G) ∧ IsPGroup 2 U ∧ t₀ ∈ U ∧ U ≤ Y ∧
      U ≤ Subgroup.centralizer ({t₀} : Set G) ∧
      (∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer ({t₀} : Set G) ⊓ Y →
        Subgroup.centralizer ({t₀} : Set G) ⊓ Y ≤ Subgroup.normalizer (P : Set G) → P ≤ U) ∧
      (∀ V : Subgroup G, Subgroup.zpowers t₀ ≤ V → V ≤ U →
        L ≤ Subgroup.normalizer (V : Set G) → V = Subgroup.zpowers t₀ ∨ V = U) ∧
      s79A r B ≤ L

@[expose] def E8AutAt (r : Row) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (B : Basis3 G (r.n + 1))
    (Y : Subgroup G), RootSetting r b₀ K E B Y →
    Nat.card ↥(ggAutomizer Y E) = Nat.card ↥(ggAutomizer ⊤ E)

@[expose] def E8TorusAt (r : Row) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (B : Basis3 G (r.n + 1))
    (Y : Subgroup G), RootSetting r b₀ K E B Y →
    ∀ x ∈ Y, orderOf x = 3 → ∃ y ∈ Y, y * x * y⁻¹ ∈ E

@[expose] def E8InvCommAt (r : Row) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (B : Basis3 G (r.n + 1))
    (Y : Subgroup G), RootSetting r b₀ K E B Y →
    ∀ s ∈ Y, orderOf s = 2 → ∃ y ∈ Y, Commute s (y * rowRootElt r B b₀ * y⁻¹)

@[expose] def E8RootCentAt (r : Row) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (B : Basis3 G (r.n + 1))
    (Y : Subgroup G), RootSetting r b₀ K E B Y →
    Subgroup.centralizer ({b₀} : Set G) ≤ Y →
    (∀ g : G, g * b₀ * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b₀ * g⁻¹ = y * b₀ * y⁻¹) →
    Subgroup.centralizer ({rowRootElt r B b₀} : Set G) ≤ Y →
    (∀ g : G, g * rowRootElt r B b₀ * g⁻¹ ∈ Y →
      ∃ y ∈ Y, g * rowRootElt r B b₀ * g⁻¹ = y * rowRootElt r B b₀ * y⁻¹) →
    ∃ (S : Subgroup G) (t : G), IsSylow2In S Y ∧ t ∈ S ∧ orderOf t = 2 ∧
      (∀ s ∈ S, s * t = t * s) ∧ Subgroup.centralizer ({t} : Set G) ≤ Y

@[expose] def TwD7BetaCentAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (B : Basis3 G (Row.twD7.n + 1))
    (Y : Subgroup G), RootSetting Row.twD7 b₀ K E B Y →
    Subgroup.centralizer ({b₀} : Set G) ≤ Y →
    (∀ g : G, g * b₀ * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b₀ * g⁻¹ = y * b₀ * y⁻¹) →
    Subgroup.centralizer ({rowRootElt Row.twD7 B b₀} : Set G) ≤ Y

@[expose] def TwD7BetaTorAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (B : Basis3 G (Row.twD7.n + 1))
    (Y : Subgroup G), RootSetting Row.twD7 b₀ K E B Y →
    ∀ F : Subgroup G, F ≤ Subgroup.centralizer ({rowRootElt Row.twD7 B b₀} : Set G) ⊓ Y →
      IsElemAbelian 3 F → Nat.card F = Nat.card E →
      ∃ c ∈ Subgroup.centralizer ({rowRootElt Row.twD7 B b₀} : Set G) ⊓ Y,
        F.map (MulAut.conj c).toMonoidHom = E

end CFSG.StandardType.FrameRoute.FS81
