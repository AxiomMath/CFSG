module

public import CFSG.Quasithin.Vol2.Ch8Sec2Steps

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

@[expose] def Step828Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k →
        ((k = 1 ∧ Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
            DihedralGroup 3)) ∨
          IsPSL 2 2 k (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) ∨
          (((∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M24Code T L I) ∧ k = 1 ∧
            Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
              DihedralGroup 5))) ∧
        (∀ n : ℕ, Row711L3Nine T L I n →
          ⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h =
            ch82B (fsuV T I) h) ∧
        (Row711M24Cocode T L I →
          ⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h =
            ch82B (fsuV T I) h) ∧
        (Row711M22Code T L I →
          (⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h).relIndex
            (ch82B (fsuV T I) h) = 2) ∧
        (∀ x : G, x ^ 5 = 1 →
          x ∈ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) →
          x ∈ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) →
          (∀ y ∈ ch82I (fsuV T I) h, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 (ch82I (fsuV T I) h)) →
          (∀ y ∈ ch82LU L (ch82U (fsuV T I) h),
            x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h))) →
          ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h), x * p * x⁻¹ * p⁻¹ ∈ ch82U (fsuV T I) h) ∧
        (Row711M24Code T L I →
          Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
              DihedralGroup 5) ∧
            ¬ T ≤ Subgroup.normalizer (oTwoUpper (ch82I (fsuV T I) h) : Set G))

end CFSG.Quasithin.H13
