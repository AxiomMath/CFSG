module

public import CFSG.Quasithin.Vol2.E2StatementsAS

public section

namespace CFSG.Quasithin.E2

open CFSG.Open CFSG.QuasithinUnique

@[expose] def KGBenderInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K : Subgroup G) (n : ℕ), MinParabolic X T M →
    kerIn M X = ⊥ → K ≤ X → X ≤ Subgroup.normalizer (K : Set G) →
    X ⊓ Subgroup.centralizer (K : Set G) = ⊥ → K ⊔ T = X → IsBenderOf n ↥K →
    M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
    pCoreOf 2 M ≤ K ∧
      ∀ x ∈ T ⊓ K, x ^ 2 = 1 → x ∈ Subgroup.centralizer ((T ⊓ K : Subgroup G) : Set G)

@[expose] def KGBenderInnerTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K : Subgroup G) (t : G) (n : ℕ), MinParabolic X T M →
    kerIn M X = ⊥ → t ∈ T → K ≤ X → cjSub t K ≠ K →
    X ≤ Subgroup.normalizer ((K ⊔ cjSub t K : Subgroup G) : Set G) →
    X ⊓ Subgroup.centralizer ((K ⊔ cjSub t K : Subgroup G) : Set G) = ⊥ →
    K ⊓ cjSub t K = ⊥ → ⁅K, cjSub t K⁆ = ⊥ → K ⊔ T = X → 2 ≤ n →
    (IsPSL 2 2 n ↥K ∨ IsSz n ↥K) → M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T →
    M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
    pCoreOf 2 M ≤ K ⊔ cjSub t K ∧
      ∀ x ∈ T ⊓ (K ⊔ cjSub t K), x ^ 2 = 1 →
        x ∈ Subgroup.centralizer ((T ⊓ (K ⊔ cjSub t K) : Subgroup G) : Set G)

@[expose] def KGBenderSubL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K S V : Subgroup G) (n : ℕ) (g : G), 2 ≤ n →
    IsPSL 2 2 n ↥K → IsSylowTwoOf S K → V ≤ S → V ≤ Subgroup.centralizer (S : Set G) →
    IsElemAbelian 2 V → 4 ≤ Nat.card V → g ∈ K → g ∉ Subgroup.normalizer (S : Set G) →
    ∃ k : ℕ, 2 ≤ k ∧ k ∣ n ∧
      (IsPSL 2 2 k ↥(V ⊔ B6.conjSub g V) ∨ IsSz k ↥(V ⊔ B6.conjSub g V))

@[expose] def KGBenderSubSz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K S V : Subgroup G) (n : ℕ) (g : G), 2 ≤ n →
    IsSz n ↥K → IsSylowTwoOf S K → V ≤ S → V ≤ Subgroup.centralizer (S : Set G) →
    IsElemAbelian 2 V → 4 ≤ Nat.card V → g ∈ K → g ∉ Subgroup.normalizer (S : Set G) →
    ∃ k : ℕ, 2 ≤ k ∧ k ∣ n ∧
      (IsPSL 2 2 k ↥(V ⊔ B6.conjSub g V) ∨ IsSz k ↥(V ⊔ B6.conjSub g V))

@[expose] def KGBenderSubU3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K S V : Subgroup G) (n : ℕ) (g : G), 2 ≤ n →
    IsPSU 3 2 n ↥K → IsSylowTwoOf S K → V ≤ S → V ≤ Subgroup.centralizer (S : Set G) →
    IsElemAbelian 2 V → 4 ≤ Nat.card V → g ∈ K → g ∉ Subgroup.normalizer (S : Set G) →
    ∃ k : ℕ, 2 ≤ k ∧ k ∣ n ∧
      (IsPSL 2 2 k ↥(V ⊔ B6.conjSub g V) ∨ IsSz k ↥(V ⊔ B6.conjSub g V))

@[expose] def KGBenderMax : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K S Y : Subgroup G) (n : ℕ), 2 ≤ n →
    (IsPSL 2 2 n ↥K ∨ IsSz n ↥K) → IsSylowTwoOf S K → S ≤ Y → Y ≤ K →
    Y ≤ Subgroup.normalizer (S : Set G) ∨ Y = K

@[expose] def KGL2Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K V : Subgroup G) (p e : ℕ), MinParabolic X T M →
    kerIn M X = ⊥ → K ≤ X → X ≤ Subgroup.normalizer (K : Set G) →
    X ⊓ Subgroup.centralizer (K : Set G) = ⊥ → K ⊔ T = X → p.Prime → 3 < p → (e = 1 ∨ e = 2) →
    (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) → IsPSL 2 p e ↥K →
    M ⊓ K = K ⊓ Subgroup.centralizer
      ((T ⊓ K ⊓ Subgroup.centralizer ((T ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G) →
    8 < autCard T K → V ≤ pCoreOf 2 M → IsElemAbelian 2 V → T ≤ Subgroup.normalizer (V : Set G) →
    Nat.card V ≤ 2

@[expose] def KGL2OddTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K V : Subgroup G) (t : G) (p : ℕ),
    MinParabolic X T M → kerIn M X = ⊥ → t ∈ T → K ≤ X → cjSub t K ≠ K →
    X ≤ Subgroup.normalizer ((K ⊔ cjSub t K : Subgroup G) : Set G) →
    X ⊓ Subgroup.centralizer ((K ⊔ cjSub t K : Subgroup G) : Set G) = ⊥ →
    K ⊓ cjSub t K = ⊥ → ⁅K, cjSub t K⁆ = ⊥ → K ⊔ T = X → p.Prime →
    (p % 8 = 1 ∨ p % 8 = 7) → IsPSL 2 p 1 ↥K → M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T →
    M ⊓ K = K ⊓ Subgroup.centralizer
      ((T ⊓ K ⊓ Subgroup.centralizer ((T ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G) →
    8 < autCard T K → V ≤ pCoreOf 2 M → IsElemAbelian 2 V → T ≤ Subgroup.normalizer (V : Set G) →
    4 ≤ Nat.card V → V = (V ⊓ K) ⊔ (V ⊓ cjSub t K) ∧ Nat.card ↥(V ⊓ K) = 2

@[expose] def KGL3Eps : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K V : Subgroup G) (p : ℕ), MinParabolic X T M →
    kerIn M X = ⊥ → K ≤ X → X ≤ Subgroup.normalizer (K : Set G) →
    X ⊓ Subgroup.centralizer (K : Set G) = ⊥ → K ⊔ T = X → p.Prime → p ≠ 2 →
    ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥K) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥K ∧ InducesOuter T K)) →
    M ⊓ K = K ⊓ Subgroup.centralizer
      ((T ⊓ K ⊓ Subgroup.centralizer ((T ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G) →
    V ≤ pCoreOf 2 M → IsElemAbelian 2 V → T ≤ Subgroup.normalizer (V : Set G) →
    4 ≤ Nat.card V → p = 3 ∧ ¬ V ≤ K

@[expose] def KGL3Even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K V : Subgroup G) (n : ℕ), MinParabolic X T M →
    kerIn M X = ⊥ → K ≤ X → X ≤ Subgroup.normalizer (K : Set G) →
    X ⊓ Subgroup.centralizer (K : Set G) = ⊥ → K ⊔ T = X → 1 ≤ n → IsPSL 3 2 n ↥K →
    IsDiagramNontrivial T K (T ⊓ K) →
    M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
    V ≤ pCoreOf 2 M → IsElemAbelian 2 V → T ≤ Subgroup.normalizer (V : Set G) →
    4 ≤ Nat.card V →
    2 ≤ n ∧ ∃ L : Subgroup G, L ≤ K ∧ IsPSL 2 2 n ↥L ∧ IsSylowTwoOf (T ⊓ L) L ∧
      V ≤ T ⊓ L ∧ V ≤ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) ∧
      M ⊓ L = L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)

@[expose] def E27Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K V : Subgroup G) (n : ℕ), Hyp28 X T M V →
    kerIn M X = ⊥ → K ≤ X → X ≤ Subgroup.normalizer (K : Set G) →
    X ⊓ Subgroup.centralizer (K : Set G) = ⊥ → K ⊔ T = X → 1 ≤ n → IsSp4Prime n ↥K →
    IsDiagramNontrivial T K (T ⊓ K) →
    M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) → E1.nParam X = n →
    4 ≤ Nat.card V → ∃ I : Subgroup G, ASInputs.IsInIHTVC X T M V I

end CFSG.Quasithin.E2
