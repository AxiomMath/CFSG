module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputD15
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch3Sec1L319Form
public import CFSG.Quasithin.Vol2.Ch8Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs CFSG.Quasithin
  CFSG.Quasithin.H13.L319 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.EmptyFaithfulMultiple
open scoped IsMulCommutative

@[expose] def KzLzInput_kz2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I → Row711M22Code T L I →
      ¬ autOn T (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I) →
      ∀ H : Subgroup G, IsHStar T (fsuM T L) H → fsuV T I ≤ pCoreOf 2 H →
      ∀ z : G, z ≠ 1 → z ∈ fsuV T I → z ∈ quasithinOmegaOneCenter T →
        H ≤ Subgroup.centralizer ({z} : Set G) → T ≤ Subgroup.centralizer ({z} : Set G) →
        ∃ Lz : Subgroup G, Lz ≤ Subgroup.centralizer ({z} : Set G) ∧
          T ≤ Subgroup.normalizer (Lz : Set G) ∧ Lz ∈ lFamily T ∧
          (NoThreeInCV (fsuM T L) (fsuV T I) → IsAlt 6 (↥Lz ⧸ CFSG.pCore 2 ↥Lz)) ∧
          (¬ NoThreeInCV (fsuM T L) (fsuV T I) →
            IsHat (↥Lz ⧸ CFSG.pCore 2 ↥Lz) (alternatingGroup (Fin 6)))

end CFSG.Quasithin.H13
