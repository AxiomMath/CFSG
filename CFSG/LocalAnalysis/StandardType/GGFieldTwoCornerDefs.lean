module

public import CFSG.LocalAnalysis.StandardType.GGFieldTwoDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldTwoCornerSetting {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) (y : G) (K : Subgroup G) : Prop :=
  GGConfig p B Bs x L D J ∧ GGInnerDiagOn Bs L ∧ GGInnerDiagOn Bs K ∧ GGNbr p B x D J y K ∧
    J ≤ K ∧ p = 3 ∧ GGHasLabel ⟨.twA, 5, 1⟩ (K ⧸ Subgroup.center K) ∧
    (∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ 2 ≤ labJ.n ∧
      GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)))

@[expose] def GGFieldTwoCornerRankOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGFieldTwoCornerSetting p B Bs x L D J y K →
    (∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGTPNRankOne lab ∧
      GGHasLabel lab (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K))) →
    GGHasLabel ⟨.A, 1, 3⟩ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K))

@[expose] def GGFieldTwoCornerNoSL28 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGFieldTwoCornerSetting p B Bs x L D J y K →
    ¬ GGHasLabel ⟨.A, 1, 3⟩ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K))

end CFSG.StandardType

end
