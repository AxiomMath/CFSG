module

public import Certificates.Data.Co3Pump
public meta import Certificates.Data.Co3Pump

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer

@[expose] def pairASize (_ : Unit := ()) : Nat :=
  (enumBfs 276 (pairGensA ()) keys 2000).pts.size

@[expose] def pairBSize (_ : Unit := ()) : Nat :=
  (enumBfs 276 (pairGensB ()) keys 20000).pts.size

end CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump
