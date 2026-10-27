module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Ledger
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.SporadicPerfect
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.Blueprint

theorem carrierFacts_of_ne_M
    (s : TauCeti.SporadicName) (hs : s ≠ .M) : CarrierFacts s := by
  obtain ⟨hfin, hsim⟩ := CFSG.Sporadic.Bridge.carrier_finite_simple_of_ne_M s hs
  obtain ⟨-, hperf⟩ := Karpilovsky.Proving.carrier_finite_isPerfect_of_ne_M s hs
  exact ⟨hfin, hsim, hperf, @exists_not_commute_of_perfect_simple _ _ hperf hsim⟩

theorem carrierFacts_M (hcard : Nat.card CFSG.Open.MonsterY443Derived = CFSG.Open.monsterOrder)
    (hsimple : IsSimpleGroup CFSG.Open.MonsterY443Derived) : CarrierFacts .M := by
  obtain ⟨hfin, hsim⟩ := CFSG.Sporadic.Bridge.carrier_M_finite_simple hcard hsimple
  obtain ⟨-, hperf⟩ := Karpilovsky.Proving.carrier_M_finite_isPerfect hcard hsimple
  exact ⟨hfin, hsim, hperf, @exists_not_commute_of_perfect_simple _ _ hperf hsim⟩

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
