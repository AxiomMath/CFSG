module

public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

@[expose] def KFactFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (c : X)
    (hc : c ∈ Subgroup.normalizer (K : Set X)),
    CFSG.IsQuasisimple ↥K →
    CFSG.Blueprint.EvenLieType (↥K ⧸ Subgroup.center ↥K) →
    Census3.TheoremThreeList (↥K ⧸ Subgroup.center ↥K) →
    orderOf (K.normalizerMonoidHom ⟨c, hc⟩) = 5 →
    ∀ P : Subgroup X, P ≤ K ⊓ Subgroup.centralizer ({c} : Set X) →
      P.subgroupOf (K ⊓ Subgroup.centralizer ({c} : Set X)) ∈
        thetaComponents 5 ↥(K ⊓ Subgroup.centralizer ({c} : Set X)) →
      ∀ y ∈ inSubgroup (aschbacherSolvableCore 5) P, y ^ 2 = 1 →
        ∀ k ∈ K, y * k = k * y

end CFSG.RankThree.PartOne.F106
