module

public import CFSG.Certificates.Kernel.J4.M24RsG

public section

namespace CFSG.KM24

@[expose] noncomputable def lettersLt (R : List Nat) (k2 : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => mAnd (Nat.rec (motive := fun _ => Bool) true
        (fun i acc => mAnd acc (Nat.blt (lt (pw x) i) k2)) (pn x)) ih) R

@[expose] noncomputable def rsChain (A : List Nat) (GA : Nat)
    (steps : List (Nat × (Nat × (List Nat × Nat)))) (N : Nat) (Rn : List Nat) (ng kq : Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool)
    (fun A GA => chkNext N A Rn GA ng kq)
    (fun st _ ih A GA => Prod.rec (motive := fun _ => Bool) (fun B r1 =>
      Prod.rec (motive := fun _ => Bool) (fun m r2 =>
        Prod.rec (motive := fun _ => Bool) (fun A' G' => mAnd (chkReplayG B m A A' GA G') (ih A' G'))
          r2) r1) st) steps A GA

@[expose] noncomputable def rsOk (T P k2 nc : Nat) (R0 A0 : List Nat) (G0 : Nat)
    (steps : List (Nat × (Nat × (List Nat × Nat)))) (N : Nat) (Rn : List Nat) (ng kq : Nat) : Bool :=
  mAnd (Nat.beq (Nat.mod k2 (nat_lit 2)) (nat_lit 0))
  (mAnd (Nat.blt (nat_lit 0) nc)
  (mAnd (Nat.blt (Nat.mul nc k2) (nat_lit 32768))
  (mAnd (lettersLt R0 k2)
  (mAnd (chkInit T P k2 nc R0 A0 G0)
    (rsChain A0 G0 steps N Rn ng kq)))))

end CFSG.KM24

end
