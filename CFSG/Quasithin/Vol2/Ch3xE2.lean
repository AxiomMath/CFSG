module

public import CFSG.Quasithin.Vol2.Ch3Sec1Inputs
public import CFSG.Quasithin.Background.E2Fifteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E213ThreeNonsolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G) (h : HypE28 H T M V),
    CharTwo H → ¬ Group.IsSolvable H → qhatInt H V h.elemAbelian ≤ 2

@[expose] def E215Nonsolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G) (h : HypE28 H T M V),
    CharTwo H → IsTISetIn V M → ¬ Group.IsSolvable H → qhatInt H V h.elemAbelian < 2

theorem e213Three_of_nonsolvable (hN : E213ThreeNonsolvable) : E213Three := by
  intro G _ _ H T M V h hchar
  by_cases hsolv : Group.IsSolvable H
  · exact E2_13_three_of_isSolvable h.elemAbelian h.minParabolic hsolv hchar h.le_T h.normal_T
      h.not_le_ker
  · exact hN G H T M V h hchar hsolv

theorem e215_of_nonsolvable (hN : E215Nonsolvable) : E215 := by
  intro G _ _ H T M V h hchar hTI
  by_cases hsolv : Group.IsSolvable H
  · exact E2_15_of_isSolvable h.elemAbelian h.minParabolic hsolv hchar h.le_T h.normal_T
      h.not_le_ker
  · exact hN G H T M V h hchar hTI hsolv

end CFSG.Quasithin
