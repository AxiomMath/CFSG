module

public import CFSG.Quasithin.H13.A6Statements
public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def orderThreeSubgroup (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ X ∧ orderOf x = 3}

@[expose] def IsTwoThreeGroup (X : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ Nat.card X → p = 2 ∨ p = 3

@[expose] def o2Z (L : Subgroup G) : Subgroup G :=
  ((Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map
    L.subtype

@[expose] def l0 (L : Subgroup G) : Subgroup G :=
  oTwoRes (o2Z L)

@[expose] def l1plus (T L V : Subgroup G) : Subgroup G :=
  oTwoRes ⁅L₁Of L (fsuV1 T V), T ⊓ L⁆

@[expose] def IsHatA6 (L : Subgroup G) : Prop :=
  Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧ Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 6))

@[expose] def Stmt13_3_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
      (V ⊓ Subgroup.centralizer (L : Set G) ≤ fsuV1 T V ∧
        Nat.card ↥(fsuV1 T V) = 2 * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) ∧
        ∀ W : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ W → W ≤ V →
          T ≤ Subgroup.normalizer (W : Set G) →
          Nat.card W = 2 * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) → W = fsuV1 T V) ∧
      conjClosure (fsuV1 T V) L = V ∧
      ∀ X : Subgroup G, T ≤ X → X < L ⊔ T → IsTwoThreeGroup X

@[expose] def Stmt13_3_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
      ((Nonempty (↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
          LieModel ↥(autOn L V) .PSU 3 3 1) →
        ∀ v ∈ V, v ≠ 1 →
          ¬ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
      (Nonempty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5))) →
        (∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
          H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ∧
        ∀ z : G, Subgroup.zpowers z = fsuV1 T V →
          ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
      (IsA6On L V → ∃ v ∈ fsuV1 T V, v ∉ Subgroup.centralizer (L : Set G) ∧
        ¬ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G))

@[expose] def Stmt13_3_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
      ¬ g1 T V ≤ Subgroup.normalizer (L : Set G) ∨
        (V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∧ IsA6On L V ∧
          ∃ _ : IsMulCommutative ↥V, Nat.card V = 2 ^ 5 ∧
            FFModel.Realizes (V := ↥V) (altCoreModel 6) (autOn L V) ⊤ ⊥)

@[expose] def Stmt13_3_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V →
      ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G)) ∨
        (IsHatA6 L ∧ pRank 3 (Subgroup.centralizer (V : Set G)) = 1 ∧
          l0 L = orderThreeSubgroup (Subgroup.centralizer (V : Set G)))

@[expose] def Stmt13_3_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L K H Y : Subgroup G), QTH13 G T L →
    quasithinIsFaithfulLocal T K → InH T H → ¬ H ≤ Subgroup.normalizer (K : Set G) →
    oTwoRes Y = Y → Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ Subgroup.normalizer (K : Set G) →
      ¬ K ≤ Y ⊔ centralizerMod (pCoreOf 2 K) (Subgroup.normalizer (K : Set G)) K ∧
        IsTwoThreeGroup Y

@[expose] def Stmt13_3_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H Y : Subgroup G) (v : G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V →
    InH T H → ¬ H ≤ Subgroup.normalizer (L : Set G) →
    oTwoRes Y = Y → Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) →
    v ∈ fsuV1 T V → v ∉ Subgroup.centralizer (L : Set G) →
    Y ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({v} : Set G) →
      Y = ⊥ ∨
        (autOn Y V = autOn (L₁Of L (fsuV1 T V)) V ∧
          (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) →
            Y = L₁Of L (fsuV1 T V)) ∧
          (IsHatA6 L → Y = l1plus T L V))

@[expose] def IsV2 (T V W : Subgroup G) : Prop :=
  fsuV1 T V ≤ W ∧ W ≤ V ∧ T ≤ Subgroup.normalizer (W : Set G) ∧ Nat.card W = 4

@[expose] def Stmt13_3_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    V ⊓ Subgroup.centralizer (L : Set G) = ⊥ → IsV2 T V V₂ →
    IsEmpty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5))) →
      ¬ pCoreOf 2 (g1 T V) ≤ Subgroup.centralizer (V₂ : Set G)

@[expose] def Stmt13_3_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₂ X I₂ : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    V ⊓ Subgroup.centralizer (L : Set G) = ⊥ → IsV2 T V V₂ →
    IsEmpty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5))) →
    (IsHatA6 L → X = oTwoRes ⁅L₁Of L V₂, T ⊓ L⁆) → (¬ IsHatA6 L → X = L₁Of L V₂) →
    I₂ = conjClosure (pCoreOf 2 (g1 T V)) (Subgroup.normalizer (V₂ : Set G)) →
    Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (I₂ : Set G) ∧
      I₂ = X ⊔ pCoreOf 2 (g1 T V) ∧
      I₂ ⊓ Subgroup.centralizer (V₂ : Set G) = pCoreOf 2 I₂ ∧
      Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)) ∧ oTwoRes I₂ = X ∧
      pCoreOf 2 (g1 T V) ⊓ Subgroup.centralizer (V₂ : Set G) ≤ pCoreOf 2 I₂ ∧
      pCoreOf 2 I₂ ≤ pCoreOf 2 (Subgroup.normalizer (V₂ : Set G)) ∧
      pRank 3 (Subgroup.centralizer (V₂ : Set G)) ≤ 1 ∧
      ∀ V₃ : Subgroup G, V₂ ≤ V₃ → V₃ ≤ V → T ≤ Subgroup.normalizer (V₃ : Set G) →
        Nat.card V₃ = 8 →
          Subgroup.centralizer (V₃ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
            (¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
              ⁅V, Subgroup.centralizer (V₃ : Set G)⁆ ≤ fsuV1 T V)

end CFSG.Quasithin.H13.A6
