module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteNamedInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRegionDefs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

@[expose] def GGFSxEndsInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
      GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
    (GGSecFiveWeylAt 3 B Bs x L D J CoxeterMatrix.E₇ →
      LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) →
      Nat.card Bs = 3 * Nat.card B ∧ Subgroup.center L = ⊥) ∧
    (GGSecFiveWeylAt 3 B Bs x L D J CoxeterMatrix.E₈ →
      LargeEvenMarking L (fun lab _ _ _ _ _ =>
        ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1) →
      Nat.card Bs = 3 * Nat.card B ∧ Subgroup.center L = ⊥)

@[expose] def GGFSyNonFSInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
      GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
    (GGSecFiveWeylAt 3 B Bs x L D J CoxeterMatrix.E₇ →
      LargeEvenMarking L (fun lab _ _ _ _ _ =>
        ((lab.tag = .twA ∧ lab.rank = 6) ∨ (lab.tag = .twE6 ∧ lab.rank = 0)) ∧ lab.n = 1) →
      Nat.card Bs = 3 * Nat.card B ∧
        ∃ y ∈ B, ∃ K : Subgroup G, LargeEvenIsNeighborOf 3 B x L y K ∧
          LargeEvenSStar 3 B y K ∧
          (K.subgroupOf (Subgroup.centralizer ({y} : Set G))).Normal ∧
          Subgroup.center K = ⊥ ∧
          LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1)) ∧
    (GGSecFiveWeylAt 3 B Bs x L D J CoxeterMatrix.E₈ →
      LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 8 ∧ lab.n = 1) →
      Nat.card Bs = 3 * Nat.card B ∧
        ∃ y ∈ B, ∃ K : Subgroup G, LargeEvenIsNeighborOf 3 B x L y K ∧
          LargeEvenSStar 3 B y K ∧
          (K.subgroupOf (Subgroup.centralizer ({y} : Set G))).Normal ∧
          Subgroup.center K = ⊥ ∧
          LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .E7 ∧ lab.rank = 0 ∧ lab.n = 1))

end CFSG.StandardType.FrameRoute

end
