module

public import CFSG.Quasithin.H13.Statements
public import CFSG.Quasithin.Background.BlueprintB2Defs
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

abbrev reducedAggregate (X : Subgroup G) : Subgroup G :=
  (primeReducedAggregate ↥X 2).map X.subtype

@[expose] def IsXSectionIso (X C J K : Subgroup G) : Prop :=
  ∃ (_ : (C.subgroupOf J).Normal) (_ : (C.subgroupOf K).Normal)
    (e : ↥J ⧸ C.subgroupOf J ≃* ↥K ⧸ C.subgroupOf K),
    ∀ x ∈ X, ∀ (j : ↥J) (k : ↥K) (hj : x * (j : G) * x⁻¹ ∈ J) (hk : x * (k : G) * x⁻¹ ∈ K),
      e (j : ↥J ⧸ C.subgroupOf J) = (k : ↥K ⧸ C.subgroupOf K) →
        e ((⟨x * (j : G) * x⁻¹, hj⟩ : ↥J) : ↥J ⧸ C.subgroupOf J) =
          ((⟨x * (k : G) * x⁻¹, hk⟩ : ↥K) : ↥K ⧸ C.subgroupOf K)

@[expose] def IsIrrPlusIn (X A Y I : Subgroup G) : Prop :=
  I ≤ A ∧ I ≠ ⊥ ∧ X ≤ Subgroup.normalizer (I : Set G) ∧ ⁅I, X⁆ = I ∧
    I ⊓ Subgroup.centralizer (X : Set G) < I ∧
    (∀ J : Subgroup G, I ⊓ Subgroup.centralizer (X : Set G) ≤ J → J ≤ I →
      X ≤ Subgroup.normalizer (J : Set G) →
        J = I ⊓ Subgroup.centralizer (X : Set G) ∨ J = I) ∧
    ∀ J : Subgroup G, A ⊓ Subgroup.centralizer (X : Set G) ≤ J →
      J ≤ conjClosure I Y ⊔ A ⊓ Subgroup.centralizer (X : Set G) →
      X ≤ Subgroup.normalizer (J : Set G) →
      IsXSectionIso X (A ⊓ Subgroup.centralizer (X : Set G)) J
        (I ⊔ A ⊓ Subgroup.centralizer (X : Set G)) →
        J ≤ I ⊔ A ⊓ Subgroup.centralizer (X : Set G)

structure FSU (G : Type) [Group G] [Finite G] (T L I : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : QuasithinUnique.quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  maximal : quasithinIsMaximalLocal T L
  faithful : quasithinIsFaithfulLocal T L
  quasisimple : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  irrPlus : IsIrrPlusIn (conjClosure L T) (reducedAggregate (L ⊔ T)) T I

@[expose] def Stmt13_3_2_two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), QTH13 G T L →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      T ≤ Subgroup.normalizer (K : Set G) ∧ quasithinIsMaximalLocal T K ∧
        quasithinIsMaxTwoLocal (Subgroup.normalizer (K : Set G)) ∧
        ∀ M : Subgroup G, quasithinIsMaxTwoLocal M → K ⊔ T ≤ M →
          M = Subgroup.normalizer (K : Set G)

@[expose] def Stmt13_3_2_three_fsu : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), QTH13 G T L →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      (∃ V : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V) ∧
        ∀ V : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V →
          V ≤ T ∧ T ≤ Subgroup.normalizer (V : Set G) ∧ FSU G T K V

structure Hyp14_3_1One (G : Type) [Group G] [Finite G] (T L : Subgroup G) : Prop where
  h13 : QTH13 G T L
  linear : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1
  not_sp62 : ¬ LieModel G .PSp 3 2 1
  not_u43 : ¬ LieModel G .PSU 4 3 1

abbrev fsuV1 (T V : Subgroup G) : Subgroup G :=
  V ⊓ quasithinOmegaOneCenter T

abbrev fsuU (T V : Subgroup G) : Subgroup G :=
  conjClosure V (Subgroup.normalizer (fsuV1 T V : Set G))

@[expose] def Stmt14_4_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14_3_1One G T L → FSU G T L V →
    ¬ IsMulCommutative ↥(fsuU T V) →
      Nonempty (G ≃* NativeSporadic.HS) ∨ LieModel G .G2 0 3 1

@[expose] def Stmt14_7_75 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14_3_1One G T L → FSU G T L V →
    IsMulCommutative ↥(fsuU T V) → Nonempty (G ≃* NativeSporadic.Ru)

@[expose] def StmtU43NoL32Local : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), LieModel G .PSU 4 3 1 →
    quasithinIsSylowTwo T → quasithinIsLocal T L → ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1

end CFSG.Quasithin.H13
