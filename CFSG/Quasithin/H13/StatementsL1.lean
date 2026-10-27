module

public import CFSG.Quasithin.H13.StatementsFSU
public import CFSG.Quasithin.SteinbergBQFiveCandidate
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

@[expose] def Alt12_2_2 (G : Type) [Group G] : Prop :=
  (∃ (t : StatedLieTag) (n f : ℕ), 2 ≤ f ∧
      (t = .PSL ∧ n = 3 ∨ t = .PSp ∧ n = 2 ∨ t = .PSU ∧ n = 4 ∨ t = .G2 ∧ n = 0 ∨
        t = .trialityD4 ∧ n = 0 ∨ t = .twistedF4 ∧ n = 0) ∧
      StatedLieAdmissible t n 2 f ∧ LieModel G t n 2 f) ∨
    LieModel G .PSU 5 2 2 ∨
    Nonempty (G ≃* NativeSporadic.M22) ∨ Nonempty (G ≃* NativeSporadic.M23) ∨
    Nonempty (G ≃* NativeSporadic.J4)

@[expose] def StmtFiveSelectedMenu : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
      (∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL n 2 1) ∨
      (∃ (K : Type) (_ : Field K), Nat.card K = 2 ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃*
          ↥(⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ : Subgroup (ModGL .G2 K)))) ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
        alternatingGroup (Fin 6)) ∨
      ∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ ∃ V : Subgroup G, V ≠ ⊥ ∧ IsElemAbelian 2 V ∧
        L ≤ Subgroup.normalizer (V : Set G) ∧
        pCoreOf 2 L ≤ L ⊓ Subgroup.centralizer (V : Set G) ∧
        L ⊓ Subgroup.centralizer (V : Set G) < L ∧
        ∃ φ : ↥L →* ↥(alternatingGroup (Fin n)), Function.Surjective φ ∧
          φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L

@[expose] def StmtFiveCandidateMenu : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
      SteinbergBQ.QTFiveCandidate (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def Stmt12_2_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ Alt12_2_2 G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → T ≤ Subgroup.normalizer (L : Set G) →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
      (∃ v ∈ V, v ≠ 1 ∧
        ¬ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∨
      (∃ n : ℕ, (n = 3 ∨ n = 4) ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
        LieModel G .PSL (n + 1) 2 1) ∨
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
        Nonempty (G ≃* alternatingGroup (Fin 9))) ∨
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
        Nonempty (G ≃* NativeSporadic.M24))

@[expose] def Stmt12_4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ Alt12_2_2 G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → T ≤ Subgroup.normalizer (L : Set G) →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
      ((Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
          LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
        V ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∧
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
        Nat.card V = 2 ^ 10 →
        ¬ Subgroup.centralizer ((V ⊓ quasithinOmegaOneCenter T : Subgroup G) : Set G) ≤
          Subgroup.normalizer (L : Set G))

@[expose] def Stmt12_7_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ Alt12_2_2 G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → T ≤ Subgroup.normalizer (L : Set G) →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    (∃ _ : ((Subgroup.centralizer (V : Set G)).subgroupOf L).Normal,
      CFSG.IsQuasisimple (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ∧
      Nat.card (Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L)) = 3 ∧
      Nonempty ((↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ⧸
          Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ≃*
        alternatingGroup (Fin 6))) →
      Nonempty (G ≃* NativeSporadic.M24) ∨ Nonempty (G ≃* NativeSporadic.He)

@[expose] def Stmt10_0_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → T ≤ Subgroup.normalizer (L : Set G)

@[expose] def Stmt11_0_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    ¬ ∃ n : ℕ, 1 < n ∧
      ((∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 n ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSp 2 2 n ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .G2 0 2 n)

@[expose] def Stmt4_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    M ≤ Subgroup.normalizer (L : Set G) →
    (∃ n : ℕ, 2 ≤ n ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) →
      (∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L ≤ M' → M' = M) ∧
      ∀ S : Subgroup G, S ≤ T → QuasithinUnique.IsSylowTwoOf (S ⊓ L) L →
        Subgroup.normalizer (S : Set G) ≤ M

@[expose] def Stmt3_3_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T →
      (∀ M L : Subgroup G, quasithinIsMaxTwoLocal M → T ≤ M → quasithinIsMaximalLocal T L →
        L ≤ M → CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
          Subgroup.normalizer (T : Set G) ≤ M) ∧
      ∀ L : Subgroup G, quasithinIsMaximalLocal T L →
        CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
        (quasithinIsMaxTwoLocal (Subgroup.normalizer (conjClosure L T : Set G)) ∧
          L ⊔ T ≤ Subgroup.normalizer (conjClosure L T : Set G) ∧
          ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L ⊔ T ≤ M' →
            M' = Subgroup.normalizer (conjClosure L T : Set G)) ∧
        (∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧ quasithinIsMaxTwoLocal M₁ ∧
          quasithinIsMaxTwoLocal M₂ ∧ T ≤ M₁ ∧ T ≤ M₂) ∧
        (∃ H : Subgroup G, IsHStar T (Subgroup.normalizer (conjClosure L T : Set G)) H) ∧
        Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (conjClosure L T : Set G) ∧
        ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (conjClosure L T : Set G)) H →
          IsUniqueMaxOver H T (H ⊓ Subgroup.normalizer (conjClosure L T : Set G)) ∧
          ¬ H ≤ Subgroup.normalizer (T : Set G)

end CFSG.Quasithin.H13
