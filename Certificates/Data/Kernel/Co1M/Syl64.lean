module

public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.XorSel

public section

namespace CFSG.KC.Syl64

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.XorSel

@[expose] noncomputable def mulL (E : List Nat) (N : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun e _ ih => List.cons (mulF (nat_lit 24) e N) ih) E

@[expose] noncomputable def conjL (G Gi : Nat) (E : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun e _ ih => List.cons (mulF (nat_lit 24) (mulF (nat_lit 24) G e) Gi) ih) E

@[expose] noncomputable def witK (mem : Nat → Bool) (L U : List Nat) : Bool :=
  allN (Nat.sub (pw2 (lenL L)) (nat_lit 1)) fun i => strictB (getL (nat_lit 0) U i) fun u =>
    andB (Nat.blt u (pw2 (nat_lit 24))) (andB (mem u) (notB (mem (vmF (nat_lit 24)
      (trK (nat_lit 24) (Nat.xor (idF (nat_lit 24)) (selK L (Nat.succ i)))) u))))

end CFSG.KC.Syl64

end
