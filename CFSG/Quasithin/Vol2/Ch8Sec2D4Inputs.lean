module

public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch8Sec2Statements
public import CFSG.Quasithin.Vol2.E2StatementsAS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.ASInputs

@[expose] def Res822L33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ H : Subgroup G, IsHStar T (fsuM T L) H →
        ¬ IsL33Exception (⊤ : Subgroup (E2.StarQuot (H ⊓ fsuM T L) H))
          (E2.star (H ⊓ fsuM T L) H (fsuV T I))

@[expose] def Step822M22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      Row711M22Code T L I → ¬ autOn T (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I) →
        ∀ H : Subgroup G, IsHStar T (fsuM T L) H → ¬ fsuV T I ≤ pCoreOf 2 H

end CFSG.Quasithin.H13
