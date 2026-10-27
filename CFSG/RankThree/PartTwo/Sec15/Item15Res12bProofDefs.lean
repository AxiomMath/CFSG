module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Item1523Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

structure Data1523Y4 (A : Subgroup G) (L Y : Subgroup G) (d : G) : Prop where
  mem_d : d ∈ A
  ne_d : d ≠ 1
  central_d : IsThreeCentralIn L d
  mem_k : k1523 A d ∈ scriptY4 A (lB A)
  type_k : Sec4.IsTripleCover (↥(k1523 A d) ⧸ CFSG.pCore 2 ↥(k1523 A d))
    CFSG.Blueprint.NativeSporadic.ON
  mem_x : oPrimeResidualOf 3 (Y ⊓ k1523 A d) ∈ scriptY4 A (lB A)
  eq_y : Y = oPrimeResidualOf 3 (Y ⊓ k1523 A d) ⊔ CFSG.Open.pCoreOf 2 Y
  type_y : (∃ _ : Fact (Nat.Prime 7), Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∨
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))

@[expose] def KS1523ONCent : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K X R : Subgroup H),
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
    Sec4.IsTripleCover (↥K ⧸ CFSG.pCore 2 ↥K) CFSG.Blueprint.NativeSporadic.ON →
    X ≤ K →
    ((∃ (_ : Fact (Nat.Prime 7))
        (f : ↥X →* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)),
        Function.Surjective f) ∨
      ∃ f : ↥X →* alternatingGroup (Fin 7), Function.Surjective f) →
    IsPGroup 2 R → R ≤ Subgroup.normalizer (K : Set H) →
    X ≤ Subgroup.normalizer (R : Set H) →
      ⁅R, K⁆ ≤ CFSG.Open.pCoreOf 2 K

@[expose] noncomputable def Step1523KReadY4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), ¬ MeetsY4 A (lB A) L Y →
      ∃ d : G, d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn L d ∧ Subgroup.zpowers d ∉ omegaA A ∧
        k1523 A d ∈ scriptY4 A (lB A) ∧
        Sec4.IsTripleCover (↥(k1523 A d) ⧸ CFSG.pCore 2 ↥(k1523 A d))
          CFSG.Blueprint.NativeSporadic.ON ∧
        Y = (Y ⊓ k1523 A d) ⊔ CFSG.Open.pCoreOf 2 Y ∧
        ((∃ _ : Fact (Nat.Prime 7), Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃*
            CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∨
          Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)))

@[expose] def Step1523KY4 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), ¬ MeetsY4 A (lB A) L Y → ∃ d : G, Data1523Y4 A L Y d

@[expose] def Step1523DeltaY4 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), ¬ MeetsY4 A (lB A) L Y → ∀ d : G, Data1523Y4 A L Y d →
      CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({d} : Set G) ≠ ⊥ →
      ⁅CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({d} : Set G), k1523 A d⁆ ≤
        CFSG.Open.pCoreOf 2 (k1523 A d) →
      oPrimeResidualOf 3 (Y ⊓ k1523 A d) ⊔
          (CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({d} : Set G)) =
        delta A (lB A) (oPrimeResidualOf 3 (Y ⊓ k1523 A d) ⊔
          (CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({d} : Set G)))

@[expose] def Step1523ZY4 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), ¬ MeetsY4 A (lB A) L Y → ∀ d : G, Data1523Y4 A L Y d →
      CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ →
      ∃ (c' : G) (Z : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧
        d ∉ Subgroup.zpowers c' ∧ Z ≤ Y ∧ ¬ Z ≤ CFSG.Open.pCoreOf 2 Y ∧
        ∀ F : Subgroup G, F ≤ Subgroup.closure {c', d} → Nat.card F = 3 →
          F ≠ Subgroup.zpowers d →
            Z ≤ Subgroup.centralizer
              ((CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) : Set G)

@[expose] noncomputable def Step1523KY4R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step1523KY4 A c L

@[expose] noncomputable def Step1523DeltaY4R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step1523DeltaY4 A c L

@[expose] noncomputable def Step1523ZY4R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step1523ZY4 A c L

@[expose] noncomputable def Step1523ZPickY4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), ¬ MeetsY4 A (lB A) L Y → ∀ d : G, Data1523Y4 A L Y d →
      CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ →
      ∃ b ∈ A, b ∉ Subgroup.zpowers d ∧
        ∃ S : Subgroup G, S ≤ Y ⊓ Subgroup.centralizer ({b} : Set G) ∧ IsPGroup 2 S ∧
          A ≤ Subgroup.normalizer (S : Set G) ∧ ¬ S ≤ CFSG.Open.pCoreOf 2 Y

end CFSG.RankThree.PartTwo.Sec15
