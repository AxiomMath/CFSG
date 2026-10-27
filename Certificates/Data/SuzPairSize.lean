module

public import Certificates.Data.SuzPump
public meta import Certificates.Data.SuzPump

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SuzPump

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.Sporadic.Schreier.Co3.Native

@[expose] def h1β : Array Nat := #[1408, 808, 726, 730, 1110, 169]

@[expose] def h2β : Array Nat := #[1376, 1514, 1076, 1379, 1557, 120]

@[expose] def pairEqCheckG (L : Array Level) (xA : Array Nat) (gs : Array (Array Nat)) (fuel N : Nat) :
    Bool :=
  gs.size == 2 &&
  allLt 2 (fun i => okP L gs[i]! && commA 1782 gs[i]! xA &&
    eqA 1782 (powArr 1782 gs[i]! 5) (idA 1782) && !(eqA 1782 gs[i]! (idA 1782))) &&
  let c := enumBfs 1782 gs suzFiveKeys fuel
  enumOK 1782 gs suzFiveKeys c && c.pts.size == N

@[expose] def pairEqCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  pairEqCheckG L (rebuild L xAβ) #[rebuild L h1β, rebuild L h2β] 1000 405

end CFSG.HardMathSupport.Solomon.Coordinator.SuzPump
