module

public import CFSG.RankThree.LocalRank.ThetaPlaneCentralLine
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport

public section

namespace CFSG.RankThree.Theta

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

@[expose] def twoT {X : Type*} [Group X] (B : Subgroup X) : Subgroup X :=
  ⨅ (b : X) (_ : b ∈ B) (_ : b ≠ 1), inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b} : Set X))

@[expose] def twoJ {X : Type*} [Group X] (B : Subgroup X) : Subgroup X :=
  ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1),
    ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b} : Set X)), B⁆

@[expose] def twoAlpha {X : Type*} [Group X] (B : Subgroup X) : Subgroup X :=
  twoJ B ⊔ twoT B

@[expose] def TwoStarConditionAt {X : Type*} [Group X] (A : Subgroup X) (a : X) : Prop :=
  twoAlpha ((A.subgroupOf (Subgroup.centralizer ({a} : Set X))).map
      (QuotientGroup.mk' (centralLine a))) ≤
    CFSG.pCore 2 (Subgroup.centralizer ({a} : Set X) ⧸ centralLine a)

@[expose] def TwoStarCondition {X : Type*} [Group X] (A : Subgroup X) : Prop :=
  ∀ a ∈ A, a ≠ 1 → TwoStarConditionAt A a

variable {X Y : Type*} [Group X] [Group Y]

theorem twoAlpha_map_equiv (f : X ≃* Y) (B : Subgroup X) :
    (twoAlpha B).map f.toMonoidHom = twoAlpha (B.map f.toMonoidHom) :=
  SteinbergBY.map_twoCoreAlpha f B

theorem normalizer_le_normalizer_twoAlpha (B : Subgroup X) :
    Subgroup.normalizer (B : Set X) ≤ Subgroup.normalizer (twoAlpha B : Set X) :=
  (SteinbergBY.alpha_isomorphism_transport (MulEquiv.refl X) B).2.2.2.2

end CFSG.RankThree.Theta
