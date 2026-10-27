module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.KG82CoverCore
public import CFSG.Quasithin.Vol2.Ch8Sec2Steps

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative commutatorElement

@[expose] def IsTransvectionK {K : Type} [Field K] {n : ℕ} (t : GL (Fin n) K) : Prop :=
  t ≠ 1 ∧
    ((t : Matrix (Fin n) (Fin n) K) - 1) * ((t : Matrix (Fin n) (Fin n) K) - 1) = 0 ∧
    ((t : Matrix (Fin n) (Fin n) K) - 1).rank = 1

@[expose] def GeneratedByTransvectionClass {K : Type} [Field K] {n : ℕ}
    (X : Subgroup (GL (Fin n) K)) : Prop :=
  ∃ t ∈ X, IsTransvectionK t ∧ X = Subgroup.closure {s | ∃ x ∈ X, s = x * t * x⁻¹}

@[expose] def StmtD4L3M22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → (Row711L3Nine T L I 1 ∨ Row711M22Code T L I) →
          ch82U (fsuV T I) h < ⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔
              ch82U (fsuV T I) h ∧
          (∀ C : Subgroup G, ch82U (fsuV T I) h ≤ C →
            C ≤ ⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h →
            ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (C : Set G) →
            C = ch82U (fsuV T I) h ∨
              C = ⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h) ∧
          mQuot (⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h)
              (ch82U (fsuV T I) h) = 4 ∧
          ∃ x ∈ ch82LU L (ch82U (fsuV T I) h), ∃ y ∈ ch82LU L (ch82U (fsuV T I) h),
            ∃ b ∈ ⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h,
              ⁅⁅x, y⁆, b⁆ ∉ ch82U (fsuV T I) h

end CFSG.Quasithin.H13.L829N
