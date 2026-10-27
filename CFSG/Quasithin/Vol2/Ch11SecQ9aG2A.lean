module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualG2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.QuasithinUnique.Setup.X6 (g2Index)

@[expose] def FactG2FourParabNonsolv : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 → ∀ j : Fin 2,
    ¬ Group.IsSolvable
      ↥((parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf (adjointGroup Tag.G2 K))

@[expose] def FactG2FourBorelNorm : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 →
    (parabolicSubgroup Tag.G2 K {g2Index 0} ⊓ parabolicSubgroup Tag.G2 K {g2Index 1}).subgroupOf
        (adjointGroup Tag.G2 K) ≤
      Subgroup.normalizer (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
        Subgroup ↥(adjointGroup Tag.G2 K)) : Set ↥(adjointGroup Tag.G2 K)) ∧
    Nat.card ↥(Subgroup.normalizer (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
        Subgroup ↥(adjointGroup Tag.G2 K)) : Set ↥(adjointGroup Tag.G2 K))) =
      Nat.card ↥((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) * 9

end CFSG.Quasithin.Vol2.Ch11.SecS
