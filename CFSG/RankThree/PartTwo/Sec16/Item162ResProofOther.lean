module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec16.Item162Proof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

@[expose] def Step162A7Other : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y₁ Y₂ S : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S S → L ≤ Y₁ →
      MeetsY4 A (lB A) L Y₁ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      WStarS4 A → TransOmegaThree A c →
      (Nonempty (↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁ ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁ ≃* alternatingGroup (Fin 10))) →
      (¬ ∃ g ∈ Subgroup.normalizer (A : Set G), Y₂ = Y₁.map (MulAut.conj g).toMonoidHom) →
      ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
        Subgroup.zpowers b ≠ Subgroup.zpowers c → MeetsY4 A (lB A) Lb Y₂ →
        Nonempty (↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7)) →
        Late.sectionCentralizer A Y₂ (CFSG.Open.pCoreOf 2 Y₂) = (Subgroup.zpowers b : Set G) →
          False

end CFSG.RankThree.PartTwo.Sec16
