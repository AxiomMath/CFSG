module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.Item15Steps

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1518Read : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y → (∀ X ∈ scriptY2 A, ¬ L ≤ X) →
      IsSimpleGroup ↥L →
      ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
        Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e → p ≠ 2 →
        e = 2 ∧ IsLThreeEpsAt ↥(L ⊓ Y) p 1

@[expose] noncomputable def Step1518TL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y → (∀ X ∈ scriptY2 A, ¬ L ≤ X) →
      IsSimpleGroup ↥L →
      ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
        Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e → p ≠ 2 →
        ∀ T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))
          (piOf 2), ¬ T ⊓ L ≤ Y


end CFSG.RankThree.PartTwo.Sec15
