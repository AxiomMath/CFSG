module

public import CFSG.RankThree.PartOne.S10.ThetaContract

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial

namespace MB3

@[expose] def MovingQuasisimpleSeven : Prop :=
  SchreierFor InCatalog → TwoActionInputs →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), SteinbergBM.SectionTenSetup G 7 A →
    ∀ K ∈ sectionTenZero 7 A, CFSG.IsQuasisimple K

end MB3

end CFSG.RankThree.PartOne
