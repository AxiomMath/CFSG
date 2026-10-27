module

public import CFSG.RankThree.PartTwo.Sec14.Ronan143QRouteLeaves5
public import CFSG.RankThree.PartTwo.Sec15.Sylow155NoG28
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3WRHolds

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec17

@[expose] def RouteHostJ2Lt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (b : G) (Lb : Subgroup G),
    CFSG.RankThree.PartTwo.Sec15.Sec15R G A b Lb →
    (CFSG.RankThree.PartTwo.Sec13.omegaA A).ncard < 3 →
    Nonempty (↥Lb ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥Lb ≃*
      CFSG.Blueprint.NativeSporadic.J2) →
    CFSG.RankThree.PartTwo.Sec15.Step155HostE0W A b Lb

theorem routeHostJ2Small_of_lt
    (h : RouteHostJ2Lt) : RouteHostJ2Small := by
  intro G _ _ A b Lb hb h3 hJb
  rcases lt_or_eq_of_le h3 with h3 | h3
  · exact h G A b Lb hb h3 hJb
  · exact step155HostE0W_of_noG28 CFSG.RankThree.PartTwo.item134_holds
      CFSG.RankThree.PartTwo.Sec11.Close.closed_sec4Item4_8
      CFSG.RankThree.PartTwo.Sec14.Ronan148M.concl142S14_holds
      CFSG.RankThree.PartTwo.Sec14.Ronan149.item1444S14_holds hb hJb h3
      (Sylow155R3.step155NoG28WR_holds G A b Lb hb h3 hJb)

theorem item1730_of_routeS16_leaves5b
    (h_Item316 : Sec19.Item316) (h_Item3_10 : Sec6.Item3_10)
    (h_RouteHostJ2Lt : RouteHostJ2Lt) (h_RouteHostGood : RouteHostGood) : Item1730 :=
  item1730_of_routeS16_leaves5 h_Item316 h_Item3_10 (routeHostJ2Small_of_lt h_RouteHostJ2Lt)
    h_RouteHostGood

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
