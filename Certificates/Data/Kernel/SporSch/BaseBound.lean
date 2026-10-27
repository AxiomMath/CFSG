module

public import Certificates.Data.Kernel.SporSch.StabBT

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def sideCnt (w SP R b : Nat) : Nat :=
  foldN (rcnt R) (fun k acc =>
    nIf(bIf(inS SP b, inS SP (rpt w (mask w) R k), Bool.not (inS SP (rpt w (mask w) R k))),
      Nat.succ acc, acc)) (nat_lit 0)

@[expose] noncomputable def bbProd (w SP : Nat) (LR : Nat → Nat) (BP nb : Nat) : Nat :=
  foldN nb (fun i acc => Nat.mul acc (sideCnt w SP (LR i) (pg w (mask w) BP i))) (nat_lit 1)

@[expose] noncomputable def bbMask (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) x)) L

@[expose] noncomputable def maskOK (n SP : Nat) (L : List Nat) : Bool :=
  bAnd(CFSG.KS.Mathieu.allLtN n L, Nat.beq (bbMask L) SP)

end CFSG.KS.SporSch

end
