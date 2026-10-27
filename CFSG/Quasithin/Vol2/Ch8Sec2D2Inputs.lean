module

public import CFSG.Quasithin.Vol2.Ch8Sec2Steps

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

@[expose] def Step829L3M22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → (Row711L3Nine T L I 1 ∨ Row711M22Code T L I) →
          T ≤ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G)

@[expose] def Step829Cocode : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → Row711M24Cocode T L I →
          T ≤ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G)

end CFSG.Quasithin.H13
