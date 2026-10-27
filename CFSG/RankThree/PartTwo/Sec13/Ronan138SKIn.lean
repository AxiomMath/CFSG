module

public import CFSG.RankThree.PartTwo.Sec13.Item138N

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Step138ENeD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → Sec8.IsZ3PGLThreePi (lBarA c L E) → E ⊓ L ∉ omegaA E

@[expose] def Step138NoCompF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → Sec8.IsZ3PGLThreePi (lBarA c L E) → ∀ F : Subgroup G, IsF138N L E F →
    ∀ (e : G) (K : Subgroup G), Subgroup.zpowers e ∈ omegaA E → K ∈ lA E e → e ∉ F →
      thetaComponents 3 ↥(K ⊓ Subgroup.centralizer ({c} : Set G)) = ∅

@[expose] def KF138TypeTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → Sec8.IsZ3PGLThreePi (lBarA c L E) →
    ∀ e ∈ E, e ∉ Subgroup.zpowers c ⊔ (E ⊓ L) →
      E ⊓ L ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) ∧
      IsQuasisimple (↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G))) ⧸
        aschbacherSolvableCore 3
          ↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G))))

end CFSG.RankThree.PartTwo.Sec13

