module

public import Certificates.Data.Kernel.Cert690.Base

public section

namespace CFSG.KC.C690

@[expose] noncomputable def orK (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def enumParK (getE : Nat → Nat) (gs : List Nat) (E : List Nat) :
    List (Nat × Nat) → Nat → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Nat → Bool)
    (fun P _ => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) P)
    (fun x _ ih P i => List.rec (motive := fun _ => Bool) false
      (fun p P' _ => andK (orK (Nat.beq i (nat_lit 0)) (andK (Nat.blt p.1 i)
          (andK (Nat.blt p.2 gs.length) (Nat.beq x (mulF (getE p.1) (gs.getD p.2 (nat_lit 0)))))))
        (ih P' (Nat.succ i))) P) E

@[expose] noncomputable def enumClG (ix : Nat → Nat) (n x : Nat) (gs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun g _ ih => andK (Nat.blt (ix (mulF x g)) n) ih) gs

@[expose] noncomputable def enumClK (ix : Nat → Nat) (n : Nat) (gs : List Nat) (E : List Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andK (enumClG ix n x gs) ih) E

@[expose] noncomputable def enumInvG (g : Nat) (E : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun e _ ih => orK (Nat.beq (mulF g e) oneF) ih) E

@[expose] noncomputable def enumInvK (gs E : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun g _ ih => andK (enumInvG g E) ih) gs

end CFSG.KC.C690

end
