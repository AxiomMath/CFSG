module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.Blueprint.Catalog
public import CFSG.LargeExtraspecial.BridgeConclusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Yardstones.M3aba7dc4b8a8

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.Blueprint.NativeSporadic
  CFSG.LargeExtraspecial.Bridge
open scoped MatrixGroups

@[expose] def GF2RankFourSetting (G : Type) [Group G] [Finite G] (z : G) : Prop :=
  (∃ a b : G, a * b ≠ b * a) ∧ CFSG.Assembly.KProper CFSG.Assembly.InCatalog G ∧
    CFSG.Assembly.IsCharTwoType G ∧ 4 ≤ CFSG.Assembly.evenRank G ∧ orderOf z = 2 ∧
    CFSG.Assembly.LargeEvenIsMaxTwoLocal (Subgroup.centralizer ({z} : Set G)) ∧
    CFSG.Assembly.LargeEvenSymplecticType
      (CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ∧
    ∃ B : Subgroup G, CFSG.Assembly.LargeEvenIsBmax 3 B ∧ B ≤ Subgroup.centralizer ({z} : Set G)

abbrev coreQ {G : Type} [Group G] (z : G) : Subgroup G :=
  inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))

@[expose] def ZWeaklyClosedInCore {G : Type} [Group G] (z : G) : Prop :=
  ∀ g : G, g⁻¹ * z * g ∈ coreQ z → g⁻¹ * z * g = z

@[expose] def CoreReducible {G : Type} [Group G] (z : G) : Prop :=
  ∃ A : Subgroup G, (Subgroup.center (coreQ z)).map (coreQ z).subtype < A ∧ A < coreQ z ∧
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (A : Set G)

@[expose] def Aschbacher1976List (G : Type) [Group G] : Prop :=
  (∃ p f m : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 3 ≤ m ∧
      (p ^ f = 2 ^ m - 1 ∨ p ^ f = 2 ^ m + 1) ∧ LieModel G .PSL 2 p f) ∨
    (IsSporadic G .M11 ∨ LieModel G .PSL 3 3 1 ∨ LieModel G .PSU 3 3 1) ∨ IsSporadic G .HS

@[expose] def Smith1979WidthFourList (G : Type) [Group G] : Prop :=
  LieModel G .PSL 6 2 1 ∨ LieModel G .PSU 6 2 1 ∨ LieModel G .POmegaPlus 4 2 1 ∨
    LieModel G .POmegaMinus 4 2 1 ∨ LieModel G .trialityD4 0 2 1 ∨
    LieModel G .POmegaPlus 4 3 1 ∨ IsSporadic G .Co2 ∨ IsSporadic G .Co1 ∨
    IsSporadic G .Th ∨ IsSporadic G .HN

@[expose] def Smith1979WidthSixList (G : Type) [Group G] : Prop :=
  LieModel G .PSL 8 2 1 ∨ LieModel G .PSU 8 2 1 ∨ LieModel G .POmegaPlus 5 2 1 ∨
    LieModel G .POmegaMinus 5 2 1 ∨ IsSporadic G .J4 ∨ IsSporadic G .Fi24Prime

@[expose] def Aschbacher1976CenterFourCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), GF2RankFourSetting G z →
    ¬ IsExtraspecialPGroup 2 (coreQ z) → (∀ x ∈ coreQ z, x ^ 4 = 1) → Aschbacher1976List G

@[expose] def Aschbacher1976HigherCenterCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), GF2RankFourSetting G z →
    ¬ IsExtraspecialPGroup 2 (coreQ z) → (∃ x ∈ coreQ z, x ^ 4 ≠ 1) → Aschbacher1976List G

@[expose] def WidthFourWeaklyClosedCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), GF2RankFourSetting G z →
    IsExtraspecialPGroup 2 (coreQ z) → Nat.card (coreQ z) = 2 ^ 9 → ZWeaklyClosedInCore z →
      LieModel G .PSU 6 2 1 ∨ IsSporadic G .Co2

@[expose] def WidthFourReducibleCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), GF2RankFourSetting G z →
    IsExtraspecialPGroup 2 (coreQ z) → Nat.card (coreQ z) = 2 ^ 9 → ¬ ZWeaklyClosedInCore z →
      CoreReducible z → LieModel G .PSL 6 2 1

@[expose] def WidthFourIrreducibleCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), GF2RankFourSetting G z →
    IsExtraspecialPGroup 2 (coreQ z) → Nat.card (coreQ z) = 2 ^ 9 →
      ¬ ZWeaklyClosedInCore z → ¬ CoreReducible z → Smith1979WidthFourList G

@[expose] def WidthSixAlternativeFourCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), GF2RankFourSetting G z →
    IsExtraspecialPGroup 2 (coreQ z) → Nat.card (coreQ z) = 2 ^ 13 →
      ∀ (Mbar : Type) [Group Mbar],
        timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
        TimmesfeldAlt4 6 Mbar → Smith1979WidthSixList G

@[expose] def OrthogonalCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), GF2RankFourSetting G z →
    IsExtraspecialPGroup 2 (coreQ z) → ∀ w : ℕ, Nat.card (coreQ z) = 2 ^ (1 + 2 * w) →
      6 ≤ w → Even w →
      ∀ (Mbar : Type) [Group Mbar],
        timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
        ∀ q : QuadraticForm (ZMod 2) (Fin w → ZMod 2), timmesfeldNondegenerate q →
          (Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
            Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q)) →
          (timmesfeldPlusType q → LieModel G .POmegaPlus ((w + 4) / 2) 2 1) ∧
            (¬ timmesfeldPlusType q → LieModel G .POmegaMinus ((w + 4) / 2) 2 1)

@[expose] def WidthTenE6Case : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), GF2RankFourSetting G z →
    IsExtraspecialPGroup 2 (coreQ z) → Nat.card (coreQ z) = 2 ^ 21 →
      ∀ (Mbar : Type) [Group Mbar],
        timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
        (Nonempty (timmesfeldFStar Mbar ≃* PSL(6, ZMod 2)) → LieModel G .E6 0 2 1) ∧
          (Nonempty (timmesfeldFStar Mbar ≃* timmesfeldPSU 6) → LieModel G .twistedE6 0 2 1)

@[expose] def WidthsSixteenTwentyEightCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), GF2RankFourSetting G z →
    IsExtraspecialPGroup 2 (coreQ z) → ∀ w : ℕ, Nat.card (coreQ z) = 2 ^ (1 + 2 * w) →
      ∀ (Mbar : Type) [Group Mbar],
        timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
        IsSimpleGroup Mbar → ∀ t : Mbar, orderOf t = 2 →
          timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) →
          (w = 16 → Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 17 →
              timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
                (Equiv.Perm (Fin 3) × timmesfeldOmegaPlus 4) →
              LieModel G .E7 0 2 1) ∧
            (w = 28 → Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 33 →
              timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
                (timmesfeldOmegaPlus 6) →
              LieModel G .E8 0 2 1)

@[expose] def WidthElevenCo2Case : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), GF2RankFourSetting G z →
    IsExtraspecialPGroup 2 (coreQ z) → Nat.card (coreQ z) = 2 ^ 23 →
      ∀ (Mbar : Type) [Group Mbar],
        timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
        Nonempty (Mbar ≃* NativeSporadic.Co2) →
        IsSporadic G .B ∧
        ∃ d₀ : NativeSporadic.B, orderOf d₀ = 2 ∧ Matrix.rank (d₀.val.val - 1) = 1860 ∧
          ∃ d : G, orderOf d = 2 ∧
            Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
              Subgroup.centralizer ({d₀} : Set NativeSporadic.B))

@[expose] def WidthTwelveCo1Case : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), GF2RankFourSetting G z →
    IsExtraspecialPGroup 2 (coreQ z) → Nat.card (coreQ z) = 2 ^ 25 →
      ∀ (Mbar : Type) [Group Mbar],
        timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
        Nonempty (Mbar ≃* NativeSporadic.Co1) →
        IsSporadic G .M ∧
        ∃ d₀ : NativeSporadic.B, orderOf d₀ = 2 ∧ Matrix.rank (d₀.val.val - 1) = 1860 ∧
          ∃ a : G, CFSG.Monster.GMS.GMSDoubleF2Centralizer d₀ a

end CFSG.Yardstones.M3aba7dc4b8a8
