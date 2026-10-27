
module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J2CoverRowBase
import all CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J2CoverRowBase

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PrimaryCells
public import CFSG.Alternating.Multipliers.Small
public import Certificates.Certificate291351
public import CFSG.Sporadic.Bridge.J2
import all CFSG.Sporadic.Bridge.J2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.Blueprint CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers

theorem card_hopfMultiplier_seedGroup :
    Nat.card (hopfMultiplier CFSG.Sporadic.Bridge.J2.seedGroup) = 2 :=
  (multiplier_cyclic_of_bounds J2Cover.isPresentation_gJ2 J2Cover.j2Comm
      J2Cover.lift_j2CommWord (N := 2) J2Cover.lift_j2R3
      Certificates.certificate291351.1 Certificates.certificate291351.2.1
      Certificates.certificate291351.2.2
      (by have := CFSG.Sporadic.Bridge.J2.le_card_seedGroup; omega)).2

theorem nativeRow_J2 :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .J2)) = sporadicMultiplierOrder .J2 := by
  have h1 : Nat.card (hopfMultiplier NativeSporadic.J2) =
      Nat.card (hopfMultiplier CFSG.Sporadic.Bridge.J2.seedGroup) :=
    card_hopfMultiplier_eq_of_mulEquiv CFSG.Sporadic.Bridge.J2.nativeEquiv
  exact h1.trans card_hopfMultiplier_seedGroup

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
