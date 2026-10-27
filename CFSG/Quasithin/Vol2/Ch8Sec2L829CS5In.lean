module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Def
public import CFSG.Quasithin.Vol2.Ch8Sec2Steps

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

@[expose] def U34Facts : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X S : Subgroup Y) [X.Normal], IsPSU 3 2 2 ↥X →
    (∀ y : Y, (∀ x ∈ X, y * x = x * y) → y = 1) → IsSylowTwoOf S X →
      (∀ E : Subgroup Y, IsElemAbelian 2 E →
          X ⊓ Subgroup.normalizer (S : Set Y) ≤ Subgroup.normalizer (E : Set Y) →
          centerSub S ≤ E → E ≤ X) ∧
      ∀ g ∈ X, g ∉ Subgroup.normalizer (S : Set Y) →
        5 ∣ Nat.card ↥(X ⊓ Subgroup.centralizer
          ((centerSub S ⊔ B6.conjSub g (centerSub S) : Subgroup Y) : Set Y)) ∧
        X ⊓ Subgroup.centralizer
          ((centerSub S ⊔ B6.conjSub g (centerSub S) : Subgroup Y) : Set Y) ≤
          Subgroup.normalizer (S : Set Y)

@[expose] def Stmt8_2_8Cocode : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → Row711M24Cocode T L I →
        ∀ P U LU : Subgroup G, P = pCoreOf 2 (ch82I (fsuV T I) h) → U = ch82U (fsuV T I) h →
          LU = ch82LU L U →
          (∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ ∈ U) ∧
          (∀ w ∈ pCoreOf 2 LU, ∀ p ∈ P, ⁅w, p⁆ ∈ U) ∧
          ∀ x : G, x ∈ Subgroup.normalizer (P : Set G) → x ∈ Subgroup.normalizer (U : Set G) →
            (∃ a : ℕ, x ^ 5 ^ a = 1) → (∀ w ∈ LU, ∀ p ∈ P, ⁅⁅x, w⁆, p⁆ ∈ U) →
            (∀ w ∈ ch82I (fsuV T I) h, ∀ p ∈ P, ⁅⁅x, w⁆, p⁆ ∈ U) → ∀ p ∈ P, ⁅x, p⁆ ∈ U

@[expose] def C6Odd829 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I → Row711M24Cocode T L I →
      ∀ B : Subgroup G, B ≤ fsuM T L → B ≠ ⊥ → IsMulCommutative ↥B → Odd (Nat.card B) →
        B ≤ Subgroup.centralizer (fsuV T I : Set G) → Subgroup.normalizer (B : Set G) ≤ fsuM T L

end CFSG.Quasithin.H13
