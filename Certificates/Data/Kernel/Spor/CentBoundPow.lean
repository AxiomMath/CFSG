module

public import Certificates.Data.Kernel.Spor.CentBound

public section

namespace CFSG.KS.CentBound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def ubCntLK (n w m nw : Nat) (TRI : Nat → Nat) (R L : Nat) (RS O : Nat → Nat) :
    Nat :=
  strictN (rcnt R) (fun c => strictN (roff n nw R) (fun o =>
    foldUp c (fun k acc => nIf(allN L (fun l =>
        hasBit (O l) (pg w m (TRI (Nat.add o k)) (pg w m (RS l) (rpt w m R k)))),
      Nat.succ acc, acc)) (nat_lit 0)))

@[expose] noncomputable def ubPowOkK (n w m : Nat) (S SI : Nat → Nat) (kS BP nb L : Nat)
    (RS : Nat → Nat) (O : Nat → Nat → Nat) : Bool :=
  allN L (fun l => ubOkK n w m S SI kS BP nb (RS l) (O l))

@[expose] noncomputable def ubPowProdK (n w m nw : Nat) (LR TRI : Nat → Nat) (nb L : Nat)
    (RS : Nat → Nat) (O : Nat → Nat → Nat) : Nat :=
  foldUp nb (fun i acc => Nat.mul acc (ubCntLK n w m nw TRI (LR i) L RS (fun l => O l i)))
    (nat_lit 1)

end CFSG.KS.CentBound
