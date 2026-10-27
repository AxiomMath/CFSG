module

public import CFSG.LieType.ChevTwo.OrthogonalBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LieType.ChevTwo

theorem s16c167_oddCore_eq_bot_of_simple_index_le_two {O : Type} [Group O] [Finite O]
    {Ω : Subgroup O} (hs : IsSimpleGroup ↥Ω) (he : Even (Nat.card ↥Ω)) (hi : Ω.index ≤ 2) :
    CFSG.oddCore O = ⊥ := by
  refine CFSG.ComponentClassification.HarrisLit.eq_bot_of_odd_of_simple (A := ⊤) (B := Ω)
    (N := CFSG.oddCore O) le_top (by rwa [Subgroup.relIndex_top_right]) hs he le_top
    (fun a _ n hn => (CFSG.oddCore_normal O).conj_mem n hn a)
    CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.odd_card_oddCore

theorem s16c167_oddCore_isometryCore_of_goodQ {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → ZMod 2) → ZMod 2} (hQ : GoodQ Q) (he : Even (Nat.card ↥(StatedOmega Q))) :
    CFSG.oddCore ↥(CFSG.MatrixModel.isometryCore Q) = ⊥ := by
  rw [← isoGrp_eq_isometryCore Q]
  have hle := statedOmega_le_isoGrp Q
  refine s16c167_oddCore_eq_bot_of_simple_index_le_two
    (Ω := (StatedOmega Q).subgroupOf (isoGrp Q)) ?_ ?_ ?_
  · have := hQ.simple
    exact (Subgroup.subgroupOfEquivOfLe hle).isSimpleGroup
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact he
  · exact hQ.relIndex_eq.le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
