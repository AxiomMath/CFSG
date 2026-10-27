module

public import CFSG.Open.FusionDefs

public section

namespace CFSG.Open

open CFSG.Open

open scoped MatrixGroups

@[expose] def fusionBenderBorel (G : Type*) [Group G] (q k : ℕ) : Prop :=
  ∀ Q : Sylow 2 G,
    fusionStronglyEmbedded (Subgroup.normalizer ((Q : Subgroup G) : Set G)) ∧
    (∃ D : Subgroup G, IsCyclic D ∧ Odd (Nat.card D) ∧ (Q : Subgroup G) ⊓ D = ⊥ ∧
      (Q : Subgroup G) ⊔ D = Subgroup.normalizer ((Q : Subgroup G) : Set G)) ∧
    (∀ z ∈ Subgroup.center (Q : Subgroup G), z ^ 2 = 1) ∧
    Nat.card (Subgroup.center (Q : Subgroup G)) = q ∧
    Nat.card (Q : Subgroup G) = q ^ k

end CFSG.Open
