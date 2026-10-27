module

public import CFSG.Timmesfeld.Bridge.RootClosureCount
public import CFSG.Timmesfeld.Bridge.RootClosureGen
public import CFSG.Timmesfeld.Bridge.RootClosureTwelve
public import CFSG.Timmesfeld.Bridge.RootClosureOddLocal

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge

@[expose] def ThirdKindThreeStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIHStruct G →
    (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) → ThirdKindThreeStmt D

theorem thirdKindStep_of (h120 : RootGenQuotientStmt) (hT : Moufang.Tim75Thm31)
    (h3 : ThirdKindThreeStep) : ThirdKindStep := by
  intro G _ D hH IH hnt d hd a ha b hb hab hnD c hc hdc hodd m hm hcu
  have := hH.finite
  have hNI := noCommonCentral_of_tim75 hT hH
  have h12 := twelve_of_thirdKindThree hH (h3 G D hH IH hnt)
  have hplus := plus_of_star hH.isClass hH.root hd
    fun u hu v hv huv huvD w hw => star_of_twelve hH hNI h12 hd hu hv huv huvD hw
  exact false_of_plus h120 hH IH hd ha hb hab hnD hc hdc hodd hm hcu hplus

theorem thirdKindStep_of_commonNeighbour (h18 : CommonNeighbourStmt) (hT : Moufang.Tim75Thm31)
    (h3 : ThirdKindThreeStep) : ThirdKindStep :=
  thirdKindStep_of (rootGenQuotientStmt_of h18) hT h3

end CFSG.Timmesfeld.Bridge.RootClosure
