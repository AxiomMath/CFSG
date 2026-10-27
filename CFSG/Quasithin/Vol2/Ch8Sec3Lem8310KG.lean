module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def KG8310MinParLn2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L S P : Subgroup X), L.Normal →
    (StatedClassicalModel ↥L .PSL 4 2 1 ∨ StatedClassicalModel ↥L .PSL 5 2 1) →
    Subgroup.centralizer (L : Set X) = ⊥ → IsSylowTwoOf S ⊤ → P ∈ uFamHat ⊤ S →
      ¬ 5 ∣ Nat.card ↥P

@[expose] def KG8310MinParHe : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L S P : Subgroup X), L.Normal →
    Nonempty (↥L ≃* NativeSporadic.Carrier .He) →
    Subgroup.centralizer (L : Set X) = ⊥ → IsSylowTwoOf S ⊤ → P ∈ uFamHat ⊤ S →
      ¬ 5 ∣ Nat.card ↥P

end CFSG.Quasithin.H13
