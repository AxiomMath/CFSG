module

public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Background.B4ModelsLie

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def altCoreModel (n : ℕ) : FFModel where
  Gam := ↥(alternatingGroup (Fin n))
  Amb := G6.PermMod n
  act σ x := G6.permAct n (σ : Equiv.Perm (Fin n)) x
  sec := G6.coreMod n
  ker := ⊥

@[expose] def IsIrreducibleUnder (L V : Subgroup G) : Prop :=
  V ≠ ⊥ ∧ ∀ W : Subgroup G, W ≤ V → L ≤ Subgroup.normalizer (W : Set G) → W = ⊥ ∨ W = V

@[expose] def IsIndecomposableUnder (L V : Subgroup G) : Prop :=
  V ≠ ⊥ ∧ ∀ A B : Subgroup G, A ≤ V → B ≤ V → L ≤ Subgroup.normalizer (A : Set G) →
    L ≤ Subgroup.normalizer (B : Set G) → A ⊓ B = ⊥ → A ⊔ B = V → A = ⊥ ∨ B = ⊥

@[expose] def Modules13_3_2 (K V : Subgroup G) [IsMulCommutative ↥V] : Prop :=
  (AlternatingNatural (V := ↥V) (autOn K V) ⊤ ⊥ 5 ∧ V ⊓ Subgroup.centralizer (K : Set G) = ⊥) ∨
    (AlternatingNatural (V := ↥V) (autOn K V) ⊤ ⊥ 6 ∧ V ⊓ Subgroup.centralizer (K : Set G) = ⊥) ∨
    (Nat.card V = 2 ^ 5 ∧ Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G)) = 2 ∧
      FFModel.Realizes (V := ↥V) (altCoreModel 6) (autOn K V) ⊤ ⊥) ∨
    (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∧ BinaryNaturalSL (V := ↥V) (autOn K V) ⊤ ⊥ 3 1 ∧
      V ⊓ Subgroup.centralizer (K : Set G) = ⊥) ∨
    (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSU 3 3 1 ∧ G2NaturalDerived (V := ↥V) (autOn K V) ⊤ ⊥ 1 ∧
      V ⊓ Subgroup.centralizer (K : Set G) = ⊥)

@[expose] def Stmt13_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), QTH13 G T L →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      QT13Five (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      (T ≤ Subgroup.normalizer (K : Set G) ∧ quasithinIsMaximalLocal T K ∧
        quasithinIsMaxTwoLocal (Subgroup.normalizer (K : Set G)) ∧
        ∀ M : Subgroup G, quasithinIsMaxTwoLocal M → K ⊔ T ≤ M →
          M = Subgroup.normalizer (K : Set G)) ∧
      ((∃ V : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V) ∧
        ∀ V : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V →
          V ≤ T ∧ T ≤ Subgroup.normalizer (V : Set G) ∧ FSU G T K V ∧
          ∃ _ : IsMulCommutative ↥V, Modules13_3_2 K V) ∧
      ((¬ quasithinO2QuotientIso K (alternatingGroup (Fin 5)) ∨
          quasithinO2QuotientIso L (alternatingGroup (Fin 5))) → QTH13 G T K)

@[expose] def Modules12_2_2 (L V : Subgroup G) [IsMulCommutative ↥V] : Prop :=
  (∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
      BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ n 1) ∨
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      Nat.card V = 2 ^ 4 ∧ IsIndecomposableUnder L V) ∨
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
      Nat.card V = 2 ^ 10 ∧ IsIrreducibleUnder L V) ∨
    (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧
      (∃ φ : ↥L →* ↥(alternatingGroup (Fin n)), Function.Surjective φ ∧
        φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L) ∧
      AlternatingNatural (V := ↥V) (autOn L V) ⊤
        ((Subgroup.centralizer (L : Set G)).subgroupOf V) n) ∨
    (Nat.card V = 2 ^ 4 ∧
      ∃ φ : ↥L →* ↥(alternatingGroup (Fin 7)), Function.Surjective φ ∧
        φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L) ∨
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 ∧
      G2NaturalDerived (V := ↥V) (autOn L V) ⊤
        ((Subgroup.centralizer (L : Set G)).subgroupOf V) 1) ∨
    (CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
        alternatingGroup (Fin 6)) ∧
      L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L ∧ Nat.card V = 2 ^ 6 ∧
      IsIrreducibleUnder L V)

@[expose] def Stmt12_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T →
      Alt12_2_2 G ∨
      ∀ L : Subgroup G, quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
        CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
          T ≤ Subgroup.normalizer (L : Set G) ∧
          (∃ V : Subgroup G, IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) ∧
          ∀ V : Subgroup G, IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
            (V ≤ T ∧ T ≤ Subgroup.normalizer (V : Set G) ∧
              IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)) ∧ FSU G T L V) ∧
            (∀ m ∈ Subgroup.normalizer (L : Set G),
              CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥) ∧
            (Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) ∨
              V ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∧
            ∃ _ : IsMulCommutative ↥V, Modules12_2_2 L V

@[expose] def Stmt12_6_34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ Alt12_2_2 G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → T ≤ Subgroup.normalizer (L : Set G) →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    (∃ φ : ↥L →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2), Function.Surjective φ ∧
      φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L) →
      Nat.card V = 2 ^ 4 ∧ L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
      ∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 4 1

end CFSG.Quasithin.H13
