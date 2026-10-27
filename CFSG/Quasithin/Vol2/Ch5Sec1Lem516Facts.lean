module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516TD

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

structure Setting516 (T L D R : Subgroup G) : Prop where
  isPGroup : IsPGroup 2 T
  le_normalizer : T ≤ Subgroup.normalizer (L : Set G)
  sylow : IsSylowTwoOf (T ⊓ L) L
  sylow_sup : IsSylowTwoOf T (L ⊔ T)
  hall : Lin2.IsHallTwoPrimeOf D (borelL T L)
  perfect : ⁅L, L⁆ = L
  simple : ∀ N : Subgroup G, N ≤ L → L ≤ Subgroup.normalizer (N : Set G) →
    N ≤ pCoreOf 2 L ∨ N = L
  le_T : R ≤ T
  reduced : IsTwoReducedIn (L ⊔ T) R
  centralizer_le : (L ⊔ T) ⊓ Subgroup.centralizer (R : Set G) ≤ T
  pCoreOf_le : pCoreOf 2 L ≤ Subgroup.centralizer (R : Set G)

@[expose] def Fact516Quot : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L D R N : Subgroup G) (n : ℕ),
    Setting516 T L D R → 2 ≤ n → N ≤ R → L ⊔ T ≤ Subgroup.normalizer (N : Set G) →
    IsNatQuotCh5 L N n →
      ∃ W : Subgroup G, W ≤ N ∧ IsTDMod T D W ∧
        (∀ hW : IsElemAbelian 2 W, qhatInt (T ⊔ D) W hW ≤ 2 → n ≤ 4) ∧
        thompsonJ T ≤ Subgroup.centralizer (W : Set G)

@[expose] def Fact516Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L D R : Subgroup G) (n : ℕ),
    Setting516 T L D R → 2 ≤ n → IsSumOfTwo L R (fun W => IsNatModCh5 L W n) →
      ∃ W : Subgroup G, W ≤ R ∧ IsTDMod T D W ∧
        ∀ hW : IsElemAbelian 2 W, qhatInt (T ⊔ D) W hW ≤ 2 → n ≤ 2

@[expose] def Fact516Orth : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L D R : Subgroup G) (m : ℕ),
    Setting516 T L D R → IsOrthCh5 L R (2 * m) → 1 ≤ m →
      Nat.card ↥(R ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) = 2 ^ m ∧
      (Odd m → T ≤ Subgroup.centralizer
        ((R ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) : Subgroup G) : Set G)) ∧
      ∀ Dp : Subgroup G, Dp ≤ D → Nat.card Dp = 2 ^ m - 1 → 2 ≤ m →
        (∀ X : Subgroup G, X ≤ Subgroup.normalizer ((borelL T L : Subgroup G) : Set G) →
          X ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) →
          X ≤ Subgroup.normalizer (((T ⊓ L) ⊔ Dp : Subgroup G) : Set G)) ∧
        IsTDMod T Dp (R ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) ∧
        ∀ hW : IsElemAbelian 2 (R ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)),
          qhatInt (T ⊔ Dp) (R ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) hW ≤ 2 →
            m ≤ 4

@[expose] def Fact516Lift (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L R S : Subgroup G),
    IsNatQuotCh5 L R n → IsElemAbelian 2 R → IsSylowTwoOf S L →
      ∀ x ∈ R, (∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Subgroup.centralizer (L : Set G)) →
        ∃ y ∈ R, y * x⁻¹ ∈ Subgroup.centralizer (L : Set G) ∧
          y ∈ Subgroup.centralizer (S : Set G)

end CFSG.Quasithin.H13
