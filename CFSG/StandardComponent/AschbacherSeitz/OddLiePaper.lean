module

public import CFSG.StandardComponent.AschbacherSeitz.OddLieNF
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal

public section

namespace CFSG.StandardComponent.AschbacherSeitz

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoOddLie

section Certified

theorem aschbacherSeitzI_oddLie_main
    (G : Type) [Group G] [Finite G] (A : Subgroup G)
    (hstd : standardComponentIsStandard A) (hO : standardComponentOddCore G = ⊥)
    (hrank : 2 ≤ CFSG.Open.pRank 2 (Subgroup.centralizer (A : Set G)))
    (hT : RankTwoOddLieType (rankTwoQuot A)) : A.Normal := by
  by_contra hN
  exact rankTwoOddLieStandardNF_of_foundation
    CFSG.ComponentClassification.RankTwoFoundation.asc76Theorem2
    CFSG.ComponentClassification.RankTwoFoundation.asc75Theorem4
    G A ⟨hstd, hN, hrank⟩ hO hT

end Certified

end CFSG.StandardComponent.AschbacherSeitz
