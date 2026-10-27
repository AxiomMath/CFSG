module

public import CFSG.RankThree.PartTwo.Census.Assembly
public import CFSG.RankThree.PartTwo.Census.OddClassical.Main
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryFourThree

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly.RankThreeEven TauCeti

theorem item433_of_evenCases
    (hspor : ∀ s : SporadicName, Item433Case (.sporadic s))
    (hAe : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid), q.p = 2 →
      Item433Case (.lie ⟨.A r q, hv⟩))
    (h2Ae : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid), q.p = 2 →
      Item433Case (.lie ⟨.twistedA r q, hv⟩))
    (hB2e : ∀ (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid), q.p = 2 →
      Item433Case (.lie ⟨.B 2 q, hv⟩))
    (hSp8 : BridgeSp8Two) (hSp64 : BridgeSp6Four) (hOp : BridgeOmega8PlusTwo)
    (hOm : BridgeOmega8MinusTwo) (hspin : SpinCarrierExclusions)
    (hexc : ExceptionalCarrierExclusions) : Item433 := by
  refine item433_of_families hspor (fun r q hv => ?_) (fun r q hv => ?_) (fun q hv => ?_)
    item433Case_C item433Case_suzuki hSp8 hSp64 hOp hOm hspin hexc
  · by_cases hq : q.p = 2
    · exact hAe r q hv hq
    · exact item433Case_A_odd r q hv hq
  · by_cases hq : q.p = 2
    · exact h2Ae r q hv hq
    · exact item433Case_twistedA_of_odd r q hv hq
  · by_cases hq : q.p = 2
    · exact hB2e q hv hq
    · exact item433Case_B2_odd q hv hq

end CFSG.RankThree.PartTwo.Census
