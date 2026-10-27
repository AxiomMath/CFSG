module

public import Certificates.Data.Kernel.Spor.BTupM

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

@[expose] noncomputable def btCntN (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc (fun a => nIf(f i, Nat.succ a, a))) n

@[expose] noncomputable def btInvP (k kw km cntL : Nat) (K R RT KL : Nat → Nat) (i : Nat) : Bool :=
  bAnd(Bool.not (Nat.beq (btDep (btRec R i)) (nat_lit 0)),
  bAnd(Nat.beq (btDep (btRec R (btMul k R RT i i))) (nat_lit 0),
    strictB (btKey kw km K i) (fun x =>
      allN cntL (fun p => Bool.not (Nat.beq x (btKey kw km KL p))))))

end CFSG.KS.BTup

end
