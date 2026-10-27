module

public import CFSG.Quasithin.Vol2.Ch8Sec2Defs
public import CFSG.Quasithin.Vol2.E2StatementsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch8Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin.ASInputs
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

@[expose] def Concl822 [Finite G] (T L I H : Subgroup G) (h : G) (k : ℕ) : Prop :=
  ¬ fsuV T I ≤ pCoreOf 2 H ∧
  h ∈ ch82I (fsuV T I) h ∧
    IsInIHTVC H T (H ⊓ fsuM T L) (fsuV T I) (ch82I (fsuV T I) h) ∧
  ch82ZI (fsuV T I) h ≠ ⊥ ∧
    ch82ZI (fsuV T I) h ≤ Subgroup.centralizer (ch82I (fsuV T I) h : Set G) ∧
  QuasithinUnique.IsSylowTwoOf (T ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ∧
    fsuM T L ⊓ ch82I (fsuV T I) h =
      ch82I (fsuV T I) h ⊓ Subgroup.normalizer (fsuV T I : Set G) ∧
  kerIn (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) = pCoreOf 2 (ch82I (fsuV T I) h) ∧
    (∃ m : ℕ, E1.nParam H = ((k * m : ℕ) : ℕ∞)) ∧
    ((k = 1 ∧ ∃ m : ℕ, Odd m ∧ 1 < m ∧
        Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
          DihedralGroup m)) ∨
      IsPSL 2 2 k (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) ∨
      IsSz k (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h))) ∧
  E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) (fsuV T I) =
      E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) (T ⊓ ch82I (fsuV T I) h) ⊓
        Subgroup.centralizer (E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)
          (T ⊓ ch82I (fsuV T I) h) :
            Set (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h))) ∧
    E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)
        (fsuM T L ⊓ ch82I (fsuV T I) h) =
      Subgroup.normalizer (E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)
        (T ⊓ ch82I (fsuV T I) h) :
          Set (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h))) ∧
  ch82A (fsuV T I) h = B6.conjSub h (fsuV T I) ⊓ Subgroup.normalizer (fsuV T I : Set G) ∧
    ch82A (fsuV T I) h ⊓ Subgroup.centralizer (fsuV T I : Set G) = ch82ZI (fsuV T I) h ∧
    ⁅⁅⁅fsuV T I, ch82A (fsuV T I) h⁆, ch82A (fsuV T I) h⁆, ch82A (fsuV T I) h⁆ = ⊥ ∧
    ¬ ch82A (fsuV T I) h ≤ Subgroup.centralizer (fsuV T I : Set G) ∧
    mQuot (ch82A (fsuV T I) h) (ch82A (fsuV T I) h ⊓ Subgroup.centralizer (fsuV T I : Set G)) +
        k = mQuot (fsuV T I) (ch82ZI (fsuV T I) h) ∧
    ch82U (fsuV T I) h ≤ ch82B (fsuV T I) h ∧
  E2.Hyp28 H T (H ⊓ fsuM T L) (fsuV T I) ∧ QuasithinUnique.CharTwo H ∧
    IsTISetIn (fsuV T I) (H ⊓ fsuM T L)

@[expose] def Stmt8_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      (∃ H : Subgroup G, IsHStar T (fsuM T L) H) ∧
      ∀ H : Subgroup G, IsHStar T (fsuM T L) H →
        (∃ h ∈ H, IsInIHTVC H T (H ⊓ fsuM T L) (fsuV T I) (ch82I (fsuV T I) h) ∧
          h ∈ ch82I (fsuV T I) h) ∧
        ∀ h ∈ H, IsInIHTVC H T (H ⊓ fsuM T L) (fsuV T I) (ch82I (fsuV T I) h) →
          h ∈ ch82I (fsuV T I) h → ∃ k : ℕ, Concl822 T L I H h k

theorem exists_concl822_of_82 (h822 : Stmt8_2_2) {G : Type} [Group G] [Finite G]
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I) :
    ∃ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H ∧ h ∈ H ∧
      Concl822 T L I H h k := by
  obtain ⟨⟨H, hH⟩, hall⟩ := h822 G T L I hyp h731 h821 hc hrow
  obtain ⟨⟨h, hh, hIC, hhI⟩, hall'⟩ := hall H hH
  obtain ⟨k, hC⟩ := hall' h hh hIC hhI
  exact ⟨H, h, k, hH, hh, hC⟩

@[expose] def Concl825 (T L I : Subgroup G) [IsMulCommutative ↥(fsuV T I)] (h : G) (k : ℕ) :
    Prop :=
  wParam T (fsuV T I) = (k : ℕ∞) ∧ IsWOffender T (fsuV T I) (ch82A (fsuV T I) h) ∧
  (∀ n : ℕ, Row711L3Nine T L I n → n = 1) ∧
  ((∃ n : ℕ, Row711L3Nine T L I n) → wParam T (fsuV T I) = 1 ∧ rParam (fsuV T I) = 5 ∧
      mQuot (ch82A (fsuV T I) h)
        (ch82A (fsuV T I) h ⊓ Subgroup.centralizer (fsuV T I : Set G)) = 4 ∧
      rk ↥(ch82U (fsuV T I) h) = 4) ∧
  (Row711M22Code T L I → wParam T (fsuV T I) = 1 ∧ rParam (fsuV T I) = 6 ∧
      mQuot (ch82A (fsuV T I) h)
        (ch82A (fsuV T I) h ⊓ Subgroup.centralizer (fsuV T I : Set G)) = 5 ∧
      rk ↥(ch82U (fsuV T I) h) = 4) ∧
  (Row711M24Code T L I → wParam T (fsuV T I) = 1 ∧ rParam (fsuV T I) = 7 ∧
      mQuot (ch82A (fsuV T I) h)
        (ch82A (fsuV T I) h ⊓ Subgroup.centralizer (fsuV T I : Set G)) = 6 ∧
      rk ↥(ch82U (fsuV T I) h) = 4) ∧
  (Row711M24Cocode T L I → wParam T (fsuV T I) = 2 ∧ rParam (fsuV T I) = 8 ∧
      mQuot (ch82A (fsuV T I) h)
        (ch82A (fsuV T I) h ⊓ Subgroup.centralizer (fsuV T I : Set G)) = 6 ∧
      rk ↥(ch82U (fsuV T I) h) = 3) ∧
  T ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ∧
    InH T (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) ∧
    ch82U (fsuV T I) h = ch82A (fsuV T I) h ⊓ Subgroup.centralizer (fsuV T I : Set G) ∧
    ch82U (fsuV T I) h = ch82ZI (fsuV T I) h ∧
    ch82U (fsuV T I) h ≤ Subgroup.centralizer (ch82I (fsuV T I) h : Set G) ∧
    ch82I (fsuV T I) h ≤ Subgroup.centralizer (ch82U (fsuV T I) h : Set G)

@[expose] def Stmt8_2_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → Concl825 T L I h k

@[expose] def Concl828 (T L I : Subgroup G) (h : G) : Prop :=
  Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ≤
      Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G) ∧
  ⁅ch82LU L (ch82U (fsuV T I) h), Subgroup.centralizer (ch82U (fsuV T I) h : Set G)⁆ ≤
      pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h)) ∧
  ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (ch82I (fsuV T I) h : Set G) ∧
    ch82LU L (ch82U (fsuV T I) h) ≤
      Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ∧
  ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ≤ ch82B (fsuV T I) h

@[expose] def Stmt8_2_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → Concl828 T L I h

@[expose] def Concl829 (T I H : Subgroup G) (h : G) : Prop :=
  T ≤ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ∧
    H = ch82I (fsuV T I) h ⊔ T ∧
    T ≤ Subgroup.normalizer ((fsuV T I ⊔ ch82A (fsuV T I) h : Subgroup G) : Set G)

@[expose] def Stmt8_2_9_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → Concl829 T I H h

@[expose] def Stmt8_2_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
    ¬ Row711M24Code T L I → ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      pCoreOf 2 (autOn (ch8Lz L z ⊔ T) (fsuV T I)) = pCoreOf 2 (autOn (ch8Lz L z) (fsuV T I))

end CFSG.Quasithin.H13
