
module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12CoverRowBase
import all CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12CoverRowBase

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.Alternating.Multipliers.Small
public import Certificates.Certificate291350
public import CFSG.Sporadic.Bridge.M12
import all CFSG.Sporadic.Bridge.M12

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.Blueprint CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers

theorem nativeRow_M12 :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .M12)) = sporadicMultiplierOrder .M12 :=
  (multiplier_cyclic_of_bounds M12Cover.isPresentation_g12 M12Cover.m12Comm
    M12Cover.lift_m12CommWord (N := 2) M12Cover.lift_m12R3
    Certificates.certificate291350.1 Certificates.certificate291350.2.1
    Certificates.certificate291350.2.2
    (by have := CFSG.Sporadic.Bridge.M12.le_card_native; omega)).2

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
