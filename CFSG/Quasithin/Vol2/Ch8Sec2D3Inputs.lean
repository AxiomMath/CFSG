module

public import CFSG.Quasithin.Vol2.Ch8Sec2Steps
public import CFSG.Quasithin.Vol2.Ch1Xi

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

@[expose] def Step827 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k →
        ∀ K : Subgroup G, quasithinIsCComponent K
            (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) →
          ch82LU L (ch82U (fsuV T I) h) ≤ K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)

@[expose] def Step827Xi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → ((∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M22Code T L I) →
        ∀ K : Subgroup G, quasithinIsCComponent K
            (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) →
          ch82LU L (ch82U (fsuV T I) h) ≤ K → ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
          ∀ X : Subgroup G, IsXi T X → X ≤ K →
            X ≤ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) → ¬ X ≤ fsuM T L →
            Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (X : Set G) →
            (∀ K' : Subgroup G, K' ≤ K → ⁅K', X⁆ ≤ pCoreOf 2 X → Group.IsSolvable ↥K') →
            ∀ (H' : Subgroup G) (h' : G) (k' : ℕ), IsHStar T (fsuM T L) H' → H' ≤ X ⊔ T →
              h' ∈ H' → Concl822 T L I H' h' k' → False

@[expose] def Step828OneA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k →
        (((∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M22Code T L I) ∧ ∃ m : ℕ, 3 ∣ m ∧
            Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
              DihedralGroup m)) →
        ∀ K : Subgroup G, quasithinIsCComponent K
            (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) →
          ch82LU L (ch82U (fsuV T I) h) ≤ K → K = ch82LU L (ch82U (fsuV T I) h)

@[expose] def Step828OneB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k →
        ((((∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M22Code T L I) ∧ ∃ m : ℕ, ¬ 3 ∣ m ∧
            Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
              DihedralGroup m)) ∨ Row711M24Code T L I) →
        ∀ K : Subgroup G, quasithinIsCComponent K
            (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) →
          ch82LU L (ch82U (fsuV T I) h) ≤ K → K = ch82LU L (ch82U (fsuV T I) h)

end CFSG.Quasithin.H13
