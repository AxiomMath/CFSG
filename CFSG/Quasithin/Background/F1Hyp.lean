module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

universe u

variable {G : Type u} [Group G]

@[expose] def borelOf (Lj S : Subgroup G) : Subgroup G :=
  Lj ⊓ Subgroup.normalizer ((S ⊓ Lj : Subgroup G) : Set G)

structure Hyp111At (Li Lj S : Subgroup G) : Prop where
  finite : Finite ↥S
  pgroup : IsPGroup 2 S
  normalizes : S ≤ Subgroup.normalizer (Li : Set G)
  sylow : IsSylowTwoOf (S ⊓ Li) Li
  listed : IsRankOneListed (oTwoQuot ↥Li)
  borel_le : borelOf Lj S ≤ Subgroup.normalizer (Li : Set G)
  charTwo : CharTwo (Li ⊔ S ⊔ borelOf Lj S)

structure Hyp111 (L1 L2 S : Subgroup G) : Prop where
  h1 : Hyp111At L1 L2 S
  h2 : Hyp111At L2 L1 S
  o2 : pCoreOf 2 (L1 ⊔ L2 ⊔ S) = ⊥

structure RankOneAt (L S : Subgroup G) : Prop where
  borel_ne : L ⊓ Subgroup.normalizer (S : Set G) ≠ L
  unique_max : ∀ M : Subgroup G, S ≤ M → M ≤ L → M ≠ L → M ≤ Subgroup.normalizer (S : Set G)
  comm : ∀ x ∈ L ⊓ Subgroup.normalizer (S : Set G), ∀ y ∈ L ⊓ Subgroup.normalizer (S : Set G),
    x * y * x⁻¹ * y⁻¹ ∈ S

end CFSG.Quasithin
