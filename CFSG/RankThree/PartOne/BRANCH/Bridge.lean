module

public import CFSG.RankThree.PartOne.BRANCH.Outer

public section

namespace CFSG.RankThree.PartOne.BRANCH

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.FieldFix
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def ZeroStarSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), SteinbergBM.SectionTenSetup G 7 A →
    ∀ K ∈ sectionTenZeroStar 7 A,
      ∃ (X : Type) (_ : Group X) (_ : Finite X) (φ : ↥K →* X), Function.Surjective φ ∧
        φ.ker ≤ center ↥K ∧ IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧
        EvenLieTypeSmall X

theorem zeroStarSmall_of_inputs (hSchreier : SchreierFor InCatalog) (hSLB : SectionListBound)
    (hI : Item613ListIdx) (hB : ∀ (X : Type) [Group X], ListEvenItem X → EvenLieTypeSmall X)
    (h112 : InSec11Two) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hOdd : OddCenterLie) (hHR : ∀ t, TCX.HighRankFalse t) (hF : TagFixedFacts .PSL) :
    ZeroStarSmall := by
  intro G _ _ A hS K hK
  by_cases hK1 : K ∈ sectionTenOne 7 A
  · exact inner_small hSchreier hSLB hI hB hS hK hK1
  · exact outer_small hSchreier h112 hGA hOdd hHR hF hS hK
      ⟨(sectionTenZeroStar_subset 7 A).2.2.1 hK.2, hK1⟩

end CFSG.RankThree.PartOne.BRANCH
