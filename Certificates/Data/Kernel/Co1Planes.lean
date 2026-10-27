module

public import Certificates.Data.Kernel.Co1Three.Census
public import CFSG.RankThree.PartOne.SPOR.Co1PlanesData

public section

namespace CFSG.KC.Co1Planes

open CFSG.KC.Co1B CFSG.KC.Co1Census CFSG.RankThree.PartOne.SPOR

@[expose] noncomputable def conjProdK (M MI : Nat → Nat) (N T : Nat) (ws : List Nat) : Nat :=
  ws.foldr (fun k acc =>
    mulWK (mulWK (mulWK (getK M N (k - 1)) T) (getK MI N (k - 1))) acc) oneK

@[expose] noncomputable def lineK (M MI : Nat → Nat) (N T p X : Nat) (ws : List Nat) (ex : Nat) :
    Bool :=
  ws.all (fun k => decide (1 ≤ k) && decide (k ≤ N) &&
      eqK (mulWK (getK M N (k - 1)) (getK MI N (k - 1))) oneK &&
      eqK (mulWK (getK M N (k - 1)) X) (mulWK X (getK M N (k - 1)))) &&
    !eqK (powWK (conjProdK M MI N T ws) ex) oneK &&
    eqK (powWK (powWK (conjProdK M MI N T ws) ex) p) oneK

@[expose] noncomputable def block1K (M MI : Nat → Nat) (N T : Nat) (b : Co1PlaneBlock1) : Bool :=
  decide (1 ≤ b.y) && decide (b.y ≤ N) &&
    eqK (mulWK (getK M N (b.y - 1)) T) (mulWK T (getK M N (b.y - 1))) &&
    eqK (powWK (getK M N (b.y - 1)) b.p) oneK && !eqK (getK M N (b.y - 1)) oneK &&
    lineK M MI N T b.p (getK M N (b.y - 1)) b.wit b.ex

@[expose] noncomputable def block2K (M MI : Nat → Nat) (N T : Nat) (b : Co1PlaneBlock2) : Bool :=
  decide (1 ≤ b.y1) && decide (b.y1 ≤ N) && decide (1 ≤ b.y2) && decide (b.y2 ≤ N) &&
    eqK (mulWK (getK M N (b.y1 - 1)) T) (mulWK T (getK M N (b.y1 - 1))) &&
    eqK (mulWK (getK M N (b.y2 - 1)) T) (mulWK T (getK M N (b.y2 - 1))) &&
    eqK (powWK (getK M N (b.y1 - 1)) b.p) oneK && eqK (powWK (getK M N (b.y2 - 1)) b.p) oneK &&
    eqK (mulWK (getK M N (b.y1 - 1)) (getK M N (b.y2 - 1)))
      (mulWK (getK M N (b.y2 - 1)) (getK M N (b.y1 - 1))) &&
    (List.range b.p).all (fun a => (List.range b.p).all fun c => (List.range b.p).all fun a' =>
      (List.range b.p).all fun c' => (decide (a = a') && decide (c = c')) ||
        !eqK (mulWK (powWK (getK M N (b.y1 - 1)) a) (powWK (getK M N (b.y2 - 1)) c))
          (mulWK (powWK (getK M N (b.y1 - 1)) a') (powWK (getK M N (b.y2 - 1)) c'))) &&
    b.wits.length == b.p + 1 && b.exps.length == b.p + 1 &&
    lineK M MI N T b.p (getK M N (b.y2 - 1)) (b.wits.getD 0 []) (b.exps.getD 0 0) &&
    (List.range b.p).all fun c => lineK M MI N T b.p
      (mulWK (getK M N (b.y1 - 1)) (powWK (getK M N (b.y2 - 1)) c)) (b.wits.getD (c + 1) [])
      (b.exps.getD (c + 1) 0)

@[expose] noncomputable def classK (M MI : Nat → Nat) (N : Nat) (c : Co1PlaneClass) : Bool :=
  decide (1 ≤ c.t) && decide (c.t ≤ 4) &&
    c.b1.all (block1K M MI N (getK M N (c.t - 1))) && c.b2.all (block2K M MI N (getK M N (c.t - 1)))

end CFSG.KC.Co1Planes

end
