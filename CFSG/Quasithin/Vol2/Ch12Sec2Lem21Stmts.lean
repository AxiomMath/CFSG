module

public import CFSG.Quasithin.Vol2.Ch12Sec2ChainStmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Concl12_2_20 {G : Type} [Group G] (T L V : Subgroup G) (n : ℕ) : Prop :=
  (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nat.card V = 2 ^ n ∧ autOn L V = ⊤ ∧
    (∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ n 1) ∧
    T ≤ L ⊔ (T ⊓ Subgroup.centralizer (V : Set G))

@[expose] def Pre12_2_21 {G : Type} [Group G] (T L V H P U I : Subgroup G) (h : G) (p : ℕ) :
    Prop :=
  IsHStar T (Subgroup.normalizer (L : Set G)) H ∧ Group.IsSolvable ↥H ∧
    p.Prime ∧ p ≠ 2 ∧ IsPGroup p ↥P ∧ P ≤ H ∧ ¬ p ∣ P.relIndex H ∧
    H = P ⊔ T ∧ P ⊓ Subgroup.normalizer (L : Set G) = (frattini ↥P).map P.subtype ∧
    h ∈ P ∧ h ∉ Subgroup.normalizer (L : Set G) ∧
    I = V ⊔ CFSG.conjugate V h ∧ U = pCoreOf 2 I ∧
    U = (U ⊓ V) ⊔ (U ⊓ CFSG.conjugate V h) ∧ (U ⊓ V) ⊓ (U ⊓ CFSG.conjugate V h) = ⊥ ∧
    IsElemAbelian 2 U ∧ U = ⁅U, oTwoUpper I⁆ ∧
    (∃ _ : (U.subgroupOf I).Normal, Nonempty (↥I ⧸ U.subgroupOf I ≃* DihedralGroup p)) ∧
    (U ⊓ V).relIndex V = 2 ∧
    ∃ _ : IsMulCommutative ↥V, autOn U V = transvAxis ((U ⊓ V).subgroupOf V)

@[expose] def Lem12220PickFull : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V → IsHStar T (Subgroup.normalizer (L : Set G)) H → Group.IsSolvable ↥H →
      ∃ (P U I : Subgroup G) (h : G) (p : ℕ), Pre12_2_21 T L V H P U I h p

@[expose] def Lem12221 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Concl12_2_20 T L V n →
    Pre12_2_21 T L V H P U I h p → U ≤ pCoreOf 2 H

@[expose] def Data12_2_22 {G : Type} [Group G] (V H P U W : Subgroup G) (v : G) (p : ℕ) :
    Prop :=
  v ∈ V ∧ v ∉ U ∧ v ∈ Subgroup.normalizer (P : Set G) ∧
    W = conjClosure U P ∧ W = ⁅W, P⁆ ∧ W ≤ pCoreOf 2 H ∧ IsElemAbelian 2 W ∧
    ⁅W, V⁆ = V ⊓ W ∧ (V ⊓ W).relIndex V = 2 ∧ oTwoUpper H = P ⊔ W ∧
    (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (V : Set G) ∧
    (Nat.card P = p ∨ (Nat.card P = p ^ 2 ∧ IsElemAbelian p P) ∨
      (Nat.card P = p ^ 3 ∧ ¬ IsMulCommutative ↥P))

@[expose] def Lem12222 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Concl12_2_20 T L V n →
    Pre12_2_21 T L V H P U I h p → U ≤ pCoreOf 2 H →
      ∃ (P' U' I' W : Subgroup G) (h' v : G), Pre12_2_21 T L V H P' U' I' h' p ∧
        U' ≤ pCoreOf 2 H ∧ Data12_2_22 V H P' U' W v p

@[expose] def Lem12223 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I W : Subgroup G) (h v : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Concl12_2_20 T L V n →
    Pre12_2_21 T L V H P U I h p → U ≤ pCoreOf 2 H → Data12_2_22 V H P U W v p →
      Nat.card P = p

@[expose] def Lem12223Post : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I W : Subgroup G) (h v : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Concl12_2_20 T L V n →
    Pre12_2_21 T L V H P U I h p → U ≤ pCoreOf 2 H → Data12_2_22 V H P U W v p →
    Nat.card P = p →
      U = W ∧ H ≤ Subgroup.normalizer (U : Set G) ∧ H ≤ Subgroup.normalizer (I : Set G) ∧
        I = P ⊔ U ⊔ V ∧ H = I ⊔ T ∧ U ⊓ Subgroup.centralizer (P : Set G) = ⊥ ∧
        ⁅pCoreOf 2 (L ⊔ T), U⁆ ≤ U ⊓ V

end CFSG.Quasithin.H13
