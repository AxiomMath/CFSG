module

public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def H11ThreeFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V A : Subgroup G) (m : ℕ), IsOrthCh5 L V (2 * m) →
    1 < m → A ≤ Subgroup.normalizer (V : Set G) → autOn A V ≤ autOn L V →
    IsElemAbelian 2 (autOn A V) → ¬ A ≤ Subgroup.centralizer (V : Set G) →
      (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A * 2 ^ m ≤
        (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V

@[expose] def OrthOddGalFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T V R : Subgroup G) (n : ℕ) (d : G),
    IsOrthCh5 L V n → n % 4 = 2 → IsPGroup 2 T → T ≤ Subgroup.normalizer (L : Set G) →
    T ≤ Subgroup.normalizer (V : Set G) → IsSylowTwoOf (T ⊓ L) L →
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T →
    d ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) → orderOf d = 3 →
    R ≤ T → d ∈ Subgroup.normalizer (R : Set G) →
      R ≤ (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (V : Set G))

end CFSG.Quasithin.H13
