module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSolvable
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

variable {G : Type} [Group G] [Finite G]

theorem pCore_map_eq_inf_of_normal {Q : Type*} [Group Q] [Finite Q] {Y : Subgroup Q}
    [hY : Y.Normal] :
    (CFSG.Open.pCore 2 ↥Y).map Y.subtype = Y ⊓ CFSG.Open.pCore 2 Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : (CFSG.Open.pCore 2 ↥Y).Characteristic := CFSG.LieType.BorelTits.pCore_characteristic 2
  apply le_antisymm
  · refine le_inf (map_subtype_le _) (CFSG.LieType.BorelTits.le_pCore 2 ?_
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2).map _))
    refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp fun g _ => ?_)
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hY]; exact mem_top g)
  · have hn : (Y ⊓ CFSG.Open.pCore 2 Q).Normal :=
      Subgroup.normal_inf_normal Y _
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left Subgroup.normal_subgroupOf
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2).to_le inf_le_right)

end CFSG.Quasithin.H13.NQCore
