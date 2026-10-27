module

public import Certificates.Data.K76J2MaxCheck
public import Certificates.Data.Kernel.MonsterB.NatBfsL

public section

namespace CFSG.KC.J2Max76

open Certificates.K76J2Max Certificates.G2ThreeMax CFSG.Monster.B.TwoA.Census CFSG.KC.Bfs

@[expose] def repOKL (c : NatCert) (hp : Array (Array ℕ)) (r : ℕ) : Bool :=
  let w := pathWord c 280 r
  let rp := permArr c w
  let c₃ := natBfsL (repAct hp rp) 4 0 280
  w.all (· < 5) && applyW c w 0 == r &&
    natCertOK (repAct hp rp) 4 (fun u => decide (u < 280)) 0 c₃ &&
    c₃.pts.toList.mergeSort (fun a b => decide (a ≤ b)) == List.range 280

end CFSG.KC.J2Max76
