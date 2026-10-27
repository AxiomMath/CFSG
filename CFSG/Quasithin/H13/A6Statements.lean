module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def A6CentralQuotient (L : Subgroup G) : Prop :=
  Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
    alternatingGroup (Fin 6))

@[expose] def IsA6On (L V : Subgroup G) : Prop :=
  Nonempty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 6)))

abbrev g1 (T V : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (fsuV1 T V : Set G)

abbrev v3 (T L V : Subgroup G) : Subgroup G :=
  ⁅V, T⁆ ⊔ V ⊓ Subgroup.centralizer (L : Set G)

inductive DType
  | A3
  | C3
  deriving DecidableEq

@[expose] def IsMaxSubgroupIn (X Y : Subgroup G) : Prop :=
  X < Y ∧ ∀ W : Subgroup G, X ≤ W → W ≤ Y → W = X ∨ W = Y

structure IsDSystem (D : DType) (Gs : Fin 3 → Subgroup G) : Prop where
  d1A3 : D = .A3 → quasithinO2QuotientIso (Gs 0) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  d1C3 : D = .C3 → quasithinO2QuotientIso (Gs 0) ↥(alternatingGroup (Fin 6)) ∨
    quasithinO2QuotientIso (Gs 0) (Equiv.Perm (Fin 6))
  d2one : quasithinO2QuotientIso (Gs 1)
    (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
  d2two : quasithinO2QuotientIso (Gs 2) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  d3sylow : ∀ i : Fin 3, QuasithinUnique.IsSylowTwoOf (Gs 0 ⊓ Gs 1 ⊓ Gs 2) (Gs i)
  d3max : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
    Gs i ⊓ Gs j ≠ Gs i ⊓ Gs k ∧
      ∀ X : Subgroup G, (Gs 0 ⊓ Gs 1 ⊓ Gs 2 ≤ X ∧ IsMaxSubgroupIn X (Gs i)) ↔
        (X = Gs i ⊓ Gs j ∨ X = Gs i ⊓ Gs k)
  d4gen : Gs 0 ⊔ Gs 1 ⊔ Gs 2 = ⊤
  d4core : ∀ N : Subgroup G, N.Normal → N ≤ Gs 0 ⊓ Gs 1 ⊓ Gs 2 → N = ⊥
  d5 : D = .C3 → Subgroup.center ↥(Gs 0) ≠ ⊥ ∨ 2 ^ 5 < Nat.card ↥(pCoreOf 2 (Gs 0))

@[expose] def StmtI_5_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : DType) (Gs : Fin 3 → Subgroup G), IsDSystem D Gs →
    (D = .A3 → LieModel G .PSL 4 2 1) ∧ (D = .C3 → LieModel G .PSp 3 2 1)

abbrev Q8Q8 : Type :=
  (QuaternionGroup 2 × QuaternionGroup 2) ⧸
    Subgroup.normalClosure {((QuaternionGroup.a 2 : QuaternionGroup 2),
      (QuaternionGroup.a 2 : QuaternionGroup 2))}

@[expose] def StmtU43Type : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), orderOf z = 2 →
    Nonempty (↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ≃* Q8Q8) →
    pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) : Set G) =
      Subgroup.zpowers z →
    Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) : Set G) ≤
      pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) →
    Nat.card ↥(Subgroup.centralizer ({z} : Set G)) =
      36 * Nat.card ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) →
    (∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧ g⁻¹ * z * g ≠ z ∧
      Nat.card ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ⊓
        CFSG.conjugate (pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) g) = 4) →
    LieModel G .PSU 4 3 1

@[expose] def Stmt13_4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → LieModel G .PSp 3 2 1

@[expose] def Stmt13_4_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → z ∈ fsuV1 T V →
    z ∉ Subgroup.centralizer (L : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) →
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G)) → LieModel G .PSp 3 2 1

@[expose] def Stmt13_4_10_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → z ∈ fsuV1 T V →
    z ∉ Subgroup.centralizer (L : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) →
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G))

@[expose] def Stmt13_5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), QTH13 G T L → ¬ LieModel G .PSp 3 2 1 →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
        LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨
        (Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) ∧
          Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3 ∧
          Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
            alternatingGroup (Fin 6)))) ∧
      (T ≤ Subgroup.normalizer (K : Set G) ∧ quasithinIsMaximalLocal T K) ∧
      (∃ VK : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T VK) ∧
      ∀ VK : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T VK →
        VK ≤ reducedAggregate (K ⊔ T) ∧ VK ≤ T ∧ T ≤ Subgroup.normalizer (VK : Set G) ∧
        FSU G T K VK ∧ VK ⊓ Subgroup.centralizer (K : Set G) = ⊥ ∧
        ∃ _ : IsMulCommutative ↥VK,
          AlternatingNatural (V := ↥VK) (autOn K VK) ⊤ ⊥ 5 ∨
            AlternatingNatural (V := ↥VK) (autOn K VK) ⊤ ⊥ 6 ∨
            BinaryNaturalSL (V := ↥VK) (autOn K VK) ⊤ ⊥ 3 1

@[expose] def Stmt13_5_12_six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V → ¬ LieModel G .PSp 3 2 1 →
    ¬ IsMulCommutative ↥(conjClosure (v3 T L V) (g1 T V)) → LieModel G .PSU 4 3 1

@[expose] def Stmt13_7_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V → ¬ LieModel G .PSp 3 2 1 →
    ¬ LieModel G .PSU 4 3 1 → IsMulCommutative ↥(conjClosure V (g1 T V))

@[expose] def Stmt13_8_3_34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), QTH13 G T L → A6CentralQuotient L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → ¬ LieModel G .PSp 3 2 1 →
    ¬ LieModel G .PSU 4 3 1 → ¬ IsMulCommutative ↥(conjClosure V (g1 T V))

end CFSG.Quasithin.H13.A6
