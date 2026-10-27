module

public import CFSG.Quasithin.Vol2.Ch12Sec2ChainStmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Lem12220Pick : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V → IsHStar T (Subgroup.normalizer (L : Set G)) H → Group.IsSolvable ↥H →
      ∃ h ∈ H, h ∉ Subgroup.normalizer (L : Set G) ∧
        (pCoreOf 2 (V ⊔ CFSG.conjugate V h) ⊓ V).relIndex V = 2 ∧
        ∃ _ : IsMulCommutative ↥V, autOn (pCoreOf 2 (V ⊔ CFSG.conjugate V h)) V =
          transvAxis ((pCoreOf 2 (V ⊔ CFSG.conjugate V h) ⊓ V).subgroupOf V)

@[expose] def Lem12220Transv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
    ∀ _ : IsMulCommutative ↥V, ∀ A : Subgroup ↥V, A.index = 2 → 4 ≤ Nat.card A →
      transvAxis A ≤
        autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V →
      ∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nat.card V = 2 ^ n ∧ autOn L V = ⊤ ∧
        BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ n 1 ∧
        T ≤ L ⊔ (T ⊓ Subgroup.centralizer (V : Set G))

@[expose] def Chain12_2_23 {G : Type} [Group G] (T L V H P U I : Subgroup G) (h : G)
    (n p : ℕ) : Prop :=
  IsHStar T (Subgroup.normalizer (L : Set G)) H ∧ Group.IsSolvable ↥H ∧
    (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nat.card V = 2 ^ n ∧
    T ≤ L ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) ∧ autOn L V = ⊤ ∧
    (∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ n 1) ∧
    p.Prime ∧ p ≠ 2 ∧ P = Subgroup.zpowers h ∧ orderOf h = p ∧ h ∈ H ∧
    h ∉ Subgroup.normalizer (L : Set G) ∧
    I = V ⊔ CFSG.conjugate V h ∧ U = pCoreOf 2 I ∧
    U = (U ⊓ V) ⊔ (U ⊓ CFSG.conjugate V h) ∧ (U ⊓ V) ⊓ (U ⊓ CFSG.conjugate V h) = ⊥ ∧
    IsElemAbelian 2 U ∧
    (∃ _ : (U.subgroupOf I).Normal, Nonempty (↥I ⧸ U.subgroupOf I ≃* DihedralGroup p)) ∧
    U ⊓ Subgroup.centralizer (P : Set G) = ⊥ ∧
    (U ⊓ V).relIndex V = 2 ∧
    (∃ _ : IsMulCommutative ↥V, autOn U V = transvAxis ((U ⊓ V).subgroupOf V)) ∧
    U ≤ pCoreOf 2 H ∧ U ⊓ V = pCoreOf 2 H ⊓ V ∧ oTwoUpper H = P ⊔ U ∧
    H ≤ Subgroup.normalizer (U : Set G) ∧ H ≤ Subgroup.normalizer (I : Set G) ∧
    I = P ⊔ U ⊔ V ∧ H = I ⊔ T ∧ ¬ I ≤ Subgroup.normalizer (L : Set G) ∧
    ⁅pCoreOf 2 (L ⊔ T), U⁆ ≤ U ⊓ V

@[expose] def Lem12221_23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V → IsHStar T (Subgroup.normalizer (L : Set G)) H → Group.IsSolvable ↥H →
    ∀ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) → Nat.card V = 2 ^ n → autOn L V = ⊤ →
    (∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ n 1) →
    T ≤ L ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) →
      ∃ (P U I : Subgroup G) (h : G) (p : ℕ), Chain12_2_23 T L V H P U I h n p

@[expose] def Lem12224Block : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Chain12_2_23 T L V H P U I h n p → IsLnBlock L n

end CFSG.Quasithin.H13
