module

public import Certificates.Data.Kernel.Misc.Base

public section

namespace CFSG.KC.F7Max

open CFSG.KC.Misc

@[expose] noncomputable def mulC (x y : Nat) : Nat :=
  letN (Nat.mod x 7) fun a => letN (Nat.mod (Nat.div x 7) 7) fun b =>
  letN (Nat.mod (Nat.div x 49) 7) fun c => letN (Nat.mod (Nat.div x 343) 7) fun d =>
  letN (Nat.mod y 7) fun e => letN (Nat.mod (Nat.div y 7) 7) fun f =>
  letN (Nat.mod (Nat.div y 49) 7) fun g => letN (Nat.mod (Nat.div y 343) 7) fun h =>
  Nat.add (Nat.mod (Nat.add (Nat.mul a e) (Nat.mul b g)) 7)
    (Nat.mul 7 (Nat.add (Nat.mod (Nat.add (Nat.mul a f) (Nat.mul b h)) 7)
      (Nat.mul 7 (Nat.add (Nat.mod (Nat.add (Nat.mul c e) (Nat.mul d g)) 7)
        (Nat.mul 7 (Nat.mod (Nat.add (Nat.mul c f) (Nat.mul d h)) 7))))))

@[expose] noncomputable def detNZ (x : Nat) : Bool :=
  Nat.blt 0 (Nat.mod (Nat.add (Nat.mul (Nat.mod x 7) (Nat.mod (Nat.div x 343) 7))
    (Nat.mul 6 (Nat.mul (Nat.mod (Nat.div x 7) 7) (Nat.mod (Nat.div x 49) 7)))) 7)

@[expose] noncomputable def bitB (M x : Nat) : Bool := Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 x))

@[expose] noncomputable def maskUpTo (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun c ih => letN ih fun m =>
    Bool.rec (motive := fun _ => Nat) m (Nat.lor m (Nat.shiftLeft 1 c)) (detNZ c)) k

@[expose] noncomputable def maskG : Nat := maskUpTo 2401

@[expose] noncomputable def passRUpTo (g M k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) M (fun x ih => letN ih fun m =>
    Bool.rec (motive := fun _ => Nat) m (Nat.lor m (Nat.shiftLeft 1 (mulC x g))) (bitB m x)) k

@[expose] noncomputable def passLUpTo (g M k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) M (fun x ih => letN ih fun m =>
    Bool.rec (motive := fun _ => Nat) m (Nat.lor m (Nat.shiftLeft 1 (mulC g x))) (bitB m x)) k

@[expose] noncomputable def passR (g M : Nat) : Nat := passRUpTo g M 2401

@[expose] noncomputable def passL (g M : Nat) : Nat := passLUpTo g M 2401

@[expose] noncomputable def passesR (gs : List Nat) (M : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun m => m)
    (fun g _ ih m => letN (passR g m) ih) gs M

@[expose] noncomputable def passesLR (gs : List Nat) (M : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun m => m)
    (fun g _ ih m => letN (passL g (passR g m)) ih) gs M

@[expose] noncomputable def roundsR (gs : List Nat) (k M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) M (fun _ ih => letN ih (passesR gs)) k

@[expose] noncomputable def roundsLR (gs : List Nat) (k M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) M (fun _ ih => letN ih (passesLR gs)) k

@[expose] noncomputable def uGensC : List Nat := [477, 2059]

@[expose] noncomputable def muK : Nat := roundsR uGensC 6 (Nat.shiftLeft 1 344)

@[expose] noncomputable def dcK (r : Nat) : Nat := roundsLR uGensC 4 (Nat.shiftLeft 1 r)

@[expose] noncomputable def tK (r : Nat) : Nat := roundsR [477, 2059, r] 4 (Nat.shiftLeft 1 344)

@[expose] noncomputable def coverB (a b d e m : Nat) : Bool := Nat.beq (a ||| (b ||| (d ||| e))) m

@[expose] noncomputable def eqB (a m : Nat) : Bool := Nat.beq a m

@[expose] noncomputable def coverOK : Bool := coverB muK (dcK 399) (dcK 742) (dcK 1134) maskG

@[expose] noncomputable def genOK (r : Nat) : Bool := eqB (tK r) maskG

end CFSG.KC.F7Max
