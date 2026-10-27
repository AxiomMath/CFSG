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

@[expose] noncomputable def Step1523KTypeY4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), ¬ MeetsY4 A (lB A) L Y →
      ((∃ _ : Fact (Nat.Prime 7), Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∨
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))) →
      ∀ d : G, d ∈ A → d ≠ 1 → IsThreeCentralIn L d → Subgroup.zpowers d ∉ omegaA A →
        deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
          deltaZero A (lB A) (Y ⊓ Subgroup.centralizer ({d} : Set G)) →
        Y = (Y ⊓ k1523 A d) ⊔ CFSG.Open.pCoreOf 2 Y →
        k1523 A d ∈ scriptY4 A (lB A) ∧
          Sec4.IsTripleCover (↥(k1523 A d) ⧸ CFSG.pCore 2 ↥(k1523 A d))
            CFSG.Blueprint.NativeSporadic.ON

@[expose] def KS1523NormTwo : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (X B : Subgroup H),
    ((∃ _ : Fact (Nat.Prime 7), Nonempty (↥X ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∨
      Nonempty (↥X ≃* alternatingGroup (Fin 7))) →
    IsPGroup 3 B → B ≤ Subgroup.normalizer (X : Set H) →
      ∃ U : Subgroup H, U ≤ X ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set H)

end CFSG.RankThree.PartTwo.Sec15
