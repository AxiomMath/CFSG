module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.U6.Core

public section

namespace CFSG.KC.U6Sec3

open CFSG.KC.Enum CFSG.KS.Raw

@[expose] noncomputable def prodAllK (n w m nw : Nat) (LR TR : Nat → Nat) (f : Nat → Bool) (d : Nat) :
    Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ acc => f acc)
    (fun _ ih i acc => strictB (LR i) (fun R => strictB (roff n nw R) (fun o =>
      allN (rcnt R) (fun a => strictB (pcomp n w m acc (TR (Nat.add o a))) (ih (Nat.succ i))))))
    d

@[expose] noncomputable def prodLazyK (n nw : Nat) (LR TR : Nat → Nat) (f : List Nat → Bool) (d : Nat) :
    Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → Bool) (fun _ L => f L)
    (fun _ ih i L => strictB (LR i) (fun R => strictB (roff n nw R) (fun o =>
      allN (rcnt R) (fun a => ih (Nat.succ i) (List.cons (TR (Nat.add o a)) L)))))
    d

@[expose] noncomputable def ptL (w m : Nat) (L : List Nat) (x : Nat) : Nat :=
  List.foldl (fun x t => pg w m t x) x L

@[expose] noncomputable def prodL (n w m : Nat) (L : List Nat) : Nat :=
  List.foldl (fun acc t => strictN acc fun acc => pcomp n w m t acc) (pidn n w) L

@[expose] noncomputable def mvK (M v : Nat) : Nat :=
  CFSG.KLie.CT.orN (nat_lit 6) fun r => Nat.shiftLeft
    (CFSG.KC.F4M.xorN (nat_lit 6) fun j =>
      CFSG.KC.F4M.fm (CFSG.KLie.CT.fget M (Nat.add (Nat.mul (nat_lit 6) r) j) (nat_lit 2))
        (CFSG.KC.U6.crd v j))
    (Nat.mul (nat_lit 2) r)

@[expose] noncomputable def tabK (QM QIM M UP POS P : Nat) : Bool :=
  allN (nat_lit 693) fun i => Nat.beq (pg (nat_lit 10) (CFSG.KS.mask (nat_lit 10)) P i)
    (CFSG.KC.U6.pos POS (CFSG.KC.U6.normK (mvK QM (mvK M (mvK QIM (CFSG.KC.U6.up UP i))))))

end CFSG.KC.U6Sec3

end
