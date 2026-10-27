module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22FSylow
public import CFSG.Quasithin.Vol2.Ch8Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.M22F

@[expose] def ZNormVStmt_m22f : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I → Row711M22Code T L I →
    ¬ autOn T (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I) →
    fsuM T L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (fsuV T I : Set G)

end CFSG.Quasithin.H13
