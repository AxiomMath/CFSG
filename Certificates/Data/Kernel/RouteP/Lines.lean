module

public import Certificates.Data.Kernel.RouteP.Mono
public import Certificates.Data.RouteP.Bridge

public section

namespace CFSG.KC.RouteP

open CFSG.KC CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

@[expose] def lineW (o : Nat) (l : List Int) : List Int :=
  ((pairsOf l).reverse).flatMap fun p =>
    List.replicate p.2.natAbs (if p.2 < 0 then -((p.1 + o : Nat) : Int) else ((p.1 + o : Nat) : Int))

@[expose] noncomputable def lineOK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (L : Array (List Int))
    (o : Nat) (t : Nat → Nat) (g : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (wordKOK NW KA KB (lineW o L[Nat.div g 20]!) (t (Nat.div g 20)))
    (wordOK NW (lineW o L[Nat.div g 20]!) (t (Nat.div g 20)) (Nat.mod g 20))
    (Nat.blt (Nat.mod g 20) 19)

end CFSG.KC.RouteP

end
