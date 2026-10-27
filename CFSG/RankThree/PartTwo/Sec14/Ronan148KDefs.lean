module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14

@[expose] def KF148ThetaTyped : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (C : Subgroup Γ), SectionFourHyp ↥C →
    aschbacherSolvableCore 3 ↥C = ⊥ → partTwoE ↥C = partTwoF ↥C →
    ∀ (A L K : Subgroup Γ) (c : Γ), A ≤ C → L ≤ C → Late.IsE27 A → c ∈ A → c ≠ 1 →
      IsQuasisimple ↥L → C ≤ Subgroup.normalizer (L : Set Γ) → ¬ L ≤ Subgroup.centralizer {c} →
      K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {c}) →
      A ≤ Subgroup.normalizer (K : Set Γ) →
      Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K : Set Γ) →
      aschbacherSolvableCore 3 ↥K ≤ Subgroup.center ↥K →
      Type148 (↥K ⧸ aschbacherSolvableCore 3 ↥K) →
      aschbacherSolvableCore 3 ↥K = ⊥

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
