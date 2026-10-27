module

public import Certificates.Data.Kernel.IdxFourLbarK

public section

namespace CFSG.KC.IF4T

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.IF4L

@[expose] noncomputable def q0K (n : Nat) : Bool := par6 (Nat.lor n (Nat.shiftRight n 6))

@[expose] noncomputable def thK (n : Nat) : Nat :=
  Nat.lor (Nat.shiftRight n 6) (Nat.shiftLeft (Nat.xor (Nat.land n 63) (Nat.shiftRight n 6)) 6)

@[expose] noncomputable def thPow (i n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) n (fun _ ih => thK ih) i

@[expose] noncomputable def anyD (Dm v : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun c ih => f0K v (fld Dm c) || ih) 5

@[expose] noncomputable def ptOK (Cm Dm Rm w k : Nat) : Bool :=
  let v := ap12 Cm k
  bif Nat.beq w 0 then q0K v && anyD Dm v
  else
    let i := Nat.mod (Nat.sub w 1) 3
    let ab := Nat.div (Nat.sub w 1) 3
    Nat.beq v (Nat.xor (thPow i (ap12 Dm (Nat.mod ab 32))) (ap12 Rm (Nat.div ab 32))) &&
      (Nat.beq i 0 || anyD Dm v)

@[expose] noncomputable def ptsOK (Cm Dm Rm : Nat) (ws : List Nat) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih k => ptOK Cm Dm Rm w k && ih (Nat.succ k)) ws k

@[expose] noncomputable def tOK (LP : List Nat) (VP m Cm E K Um F Am : Nat) (ws : List Nat) :
    Bool :=
  let N := Nat.xor (subP LP m) idP
  let Rm := mulP N Um
  let Dm := mulP VP Am
  Nat.beq (Nat.xor (mulP Cm E) (mulP K N)) idP && Nat.beq (mulP Rm F) N &&
    Nat.beq (mulP N Dm) 0 && allBelow 12 (fun j => Nat.blt (fld E j) 256 && Nat.blt (fld F j) 16) &&
    allBelow 16 (fun b => !q0K (ap12 Rm b)) && Nat.beq (lenN ws) 256 && ptsOK Cm Dm Rm ws 0

@[expose] noncomputable def recOK (LP : List Nat) (VP : Nat) (r ws : List Nat) : Bool :=
  tOK LP VP (nthD 0 r 0) (nthD 0 r 1) (nthD 0 r 2) (nthD 0 r 3) (nthD 0 r 4) (nthD 0 r 5)
    (nthD 0 r 6) ws

@[expose] noncomputable def maskOK (LP : List Nat) (OM : Nat) (ms : List Nat) : Bool :=
  allBelow (Nat.pow 2 (lenN LP)) fun m =>
    !Bool.xor (Nat.beq (mulP (subP LP m) OM) (mulP OM (subP LP m))) (Nat.beq m 0 || memN m ms)

end CFSG.KC.IF4T

end
