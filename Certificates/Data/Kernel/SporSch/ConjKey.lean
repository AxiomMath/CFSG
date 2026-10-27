module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Orders.Mat
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const

public section

namespace CFSG.KC.ConjKey

open CFSG.KC.Loop

@[expose] noncomputable def strictKB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def appF (vm : Nat → Nat → Nat) (G : Nat → Nat) (fuel : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ v => v)
    (fun _ ih c v => nIf(Nat.beq c (nat_lit 0), v,
      strictN (vm v (G (Nat.sub (Nat.mod c (nat_lit 8)) (nat_lit 1))))
        (fun u => ih (Nat.div c (nat_lit 8)) u))) fuel

@[expose] noncomputable def appI (vm : Nat → Nat → Nat) (GI : Nat → Nat) (fuel : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ v => v)
    (fun _ ih c v => nIf(Nat.beq c (nat_lit 0), v,
      strictN (ih (Nat.div c (nat_lit 8)) v)
        (fun u => vm u (GI (Nat.sub (Nat.mod c (nat_lit 8)) (nat_lit 1)))))) fuel

@[expose] noncomputable def keyOf (vm : Nat → Nat → Nat) (G GI : Nat → Nat) (fuel Y e c : Nat) :
    Nat :=
  strictN (appF vm G fuel c e) (fun a => strictN (vm a Y) (fun b => appI vm GI fuel c b))

@[expose] noncomputable def incK (key : Nat → Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih p => strictKB (key c) (fun k => bAnd(Nat.blt p k, ih k))) L

@[expose] noncomputable def conjKeysOK (vm : Nat → Nat → Nat) (G GI : Nat → Nat)
    (fuel Y e : Nat) (L : List Nat) (n : Nat) : Bool :=
  bAnd(Nat.beq (List.length L) n, incK (keyOf vm G GI fuel Y e) L (nat_lit 0))

@[expose] noncomputable def eqK (a b : Nat) : Bool := Nat.beq a b

@[expose] noncomputable def vmHN (v M : Nat) : Nat :=
  CFSG.KC.Ord.vecR (nat_lit 5) (nat_lit 13) (nat_lit 0x6c1) (nat_lit 0x85) (nat_lit 9)
    CFSG.KD.OrdHN.LV CFSG.KD.OrdHN.HV CFSG.KD.OrdHN.RM v M

end CFSG.KC.ConjKey

end
