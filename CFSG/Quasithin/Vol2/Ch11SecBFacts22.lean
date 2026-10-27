module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts21
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch4Sec2W4213

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def FactMParam : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X : Subgroup G) (n m : ℕ) (hV : IsElemAbelian 2 V),
    2 ≤ n → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V → NatModuleOf L V n →
    (KindG2 L V n ∧ m = 2 * n ∨ ¬ KindG2 L V n ∧ m = n) → L ≤ X →
    X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) →
      E3.mParam (autI hV X) = m ∧ 2 * m ≤ E3.mQuot V ⊥

@[expose] def FactOddCodim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X : Subgroup G) (n m : ℕ),
    IsElemAbelian 2 V → 2 ≤ n → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V →
    NatModuleOf L V n → (KindG2 L V n ∧ m = 2 * n ∨ ¬ KindG2 L V n ∧ m = n) → L ≤ X →
    X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) →
    (∀ x ∈ X ⊓ Subgroup.normalizer (V : Set G), ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 →
      x ^ p ∈ Subgroup.centralizer (V : Set G) → x ∈ L ⊔ Subgroup.centralizer (V : Set G)) →
    ∀ x ∈ X ⊓ Subgroup.normalizer (V : Set G), ∀ p : ℕ, p.Prime → p ≠ 2 →
      x ^ p ∈ Subgroup.centralizer (V : Set G) → x ∉ Subgroup.centralizer (V : Set G) →
        2 * m ≤ E3.mQuot V (V ⊓ Subgroup.centralizer ({x} : Set G))

@[expose] def FactHyperplaneT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G),
    IsElemAbelian 2 V → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V → NatModuleOf L V 2 →
    ¬ KindG2 L V 2 → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    QuasithinUnique.IsSylowTwoOf T (L ⊔ T) → T ≤ Subgroup.normalizer (V : Set G) →
    T ≤ Subgroup.normalizer (L : Set G) →
    ∀ U : Subgroup G, U ≤ V → E3.mQuot V U = 1 →
      ∃ g ∈ L, T ≤ Subgroup.normalizer (conjSubgroup U g : Set G)

@[expose] def FactSp4FourExt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G),
    IsElemAbelian 2 V → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V → NatModuleOf L V 2 →
    KindSp4 L V 2 → Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 →
    IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) →
    QuasithinUnique.IsSylowTwoOf T (L ⊔ T) → T ≤ Subgroup.normalizer (V : Set G) →
    T ≤ Subgroup.normalizer (L : Set G) →
      ¬ V ⊓ Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer (L : Set G) ∧
      ∀ U : Subgroup G, U ≤ V → E3.mQuot V U = 1 →
        U ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
          IsMaxSubgroupIn (L ⊔ T) ((L ⊔ T) ⊓ Subgroup.normalizer (U : Set G)) ∧
          ((L ⊔ T) ⊓ Subgroup.normalizer (U : Set G)).relIndex (L ⊔ T) ≠ 2 ∧
          ∃ Y : Subgroup G, Y ≤ L ⊓ Subgroup.normalizer (U : Set G) ∧ Nat.card Y = 3 ∧
            Y ⊓ Subgroup.centralizer (U : Set G) = ⊥

@[expose] def FactRootInv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T : Subgroup G) (n m : ℕ),
    IsElemAbelian 2 V → 2 ≤ n → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V →
    NatModuleOf L V n → (KindG2 L V n ∧ m = 2 * n ∨ ¬ KindG2 L V n ∧ m = n) → L ≤ X →
    X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) →
    QuasithinUnique.IsSylowTwoOf T (L ⊔ T) → T ≤ Subgroup.normalizer (V : Set G) →
    T ≤ Subgroup.normalizer (L : Set G) →
    ∀ x ∈ X ⊓ Subgroup.normalizer (V : Set G), x ^ 2 ∈ Subgroup.centralizer (V : Set G) →
      x ∉ Subgroup.centralizer (V : Set G) →
      E3.mQuot V (V ⊓ Subgroup.centralizer ({x} : Set G)) = m →
        ∃ (i : ℕ) (W : Subgroup G), W ≤ V ⊓ Subgroup.centralizer ({x} : Set G) ∧
          ((¬ KindSp4 L V n ∧ ¬ KindG2 L V n) ∧ i = 2 ∧
              W = V ⊓ Subgroup.centralizer ({x} : Set G) ∨
            (KindSp4 L V n ∨ KindG2 L V n) ∧ i = 3) ∧
          ∃ g ∈ L, V ⊓ Subgroup.centralizer (L : Set G) ≤ conjSubgroup W g ∧
            IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) (conjSubgroup W g) ∧
            (V ⊓ Subgroup.centralizer (L : Set G)).relIndex (conjSubgroup W g) = 2 ^ (n * i) ∧
            T ⊓ L ≤ Subgroup.normalizer (conjSubgroup W g : Set G)

@[expose] def FactA2InL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X : Subgroup G) (n : ℕ) (hV : IsElemAbelian 2 V),
    2 ≤ n → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V → NatModuleOf L V n → L ≤ X →
    X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) →
      ∀ A ∈ E3.aSet 2 (autI hV X), A ≤ autOn L V

@[expose] def FactFlagOneCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T U : Subgroup G) (n : ℕ),
    IsElemAbelian 2 V → 2 ≤ n → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V →
    NatModuleOf L V n → QuasithinUnique.IsSylowTwoOf T (L ⊔ T) →
    T ≤ Subgroup.normalizer (V : Set G) → T ≤ Subgroup.normalizer (L : Set G) →
    V ⊓ Subgroup.centralizer (L : Set G) ≤ U → U ≤ V →
    IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U →
    (V ⊓ Subgroup.centralizer (L : Set G)).relIndex U = 2 ^ n →
    T ≤ Subgroup.normalizer (U : Set G) →
      T ⊓ L ≤ Subgroup.centralizer (U : Set G)

@[expose] def FactNot4213 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L VB : Subgroup G) (n : ℕ), 2 ≤ n →
    RankTwoShape (↥L ⧸ CFSG.pCore 2 ↥L) n → ¬ (Concl443TwoI G T M L VB ∨ Orth4213 G M L VB)

end CFSG.Quasithin.Vol2.Ch11.SecB
