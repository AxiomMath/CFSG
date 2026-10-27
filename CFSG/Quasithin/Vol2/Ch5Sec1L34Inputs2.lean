module

public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def L34AutNoNineFact : Prop :=
  ∀ (X : Type) [Group X], LieModel X .PSL 3 2 2 → ∀ α : MulAut X, α ^ 9 = 1 → α ^ 3 = 1

@[expose] def OrthTorusFixFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L W S : Subgroup G) (m : ℕ) (d w : G),
    IsOrthCh5 L W (2 * m) → Even m → IsSylowTwoOf S L →
    IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (W : Set G)) →
    d ∈ L ⊓ Subgroup.normalizer (S : Set G) → orderOf d = 3 →
    w ∈ W → w ∈ Subgroup.centralizer (S : Set G) → d * w * d⁻¹ = w → w = 1

end CFSG.Quasithin.H13
