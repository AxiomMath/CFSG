module

public import Certificates.Data.Kernel.F2Word

public section

namespace CFSG.KC.S63K

@[expose] noncomputable def eqM (A B : Nat) : Bool := Nat.beq (A % 2 ^ 576) (B % 2 ^ 576)

@[expose] noncomputable def pickK (F : Nat → Nat) (t : Nat) (k : Nat) :
    Nat → List Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat → List Nat) (fun _ _ P => P.reverse)
    (fun _ ih c E P =>
      bif Nat.ble t E.length then P.reverse
      else bif E.any (fun e => eqM e (F c)) then ih (c + 1) E P
      else ih (c + 1) (E ++ E.map (CFSG.KC.F2W.mulW 24 (F c))) (c :: P)) k

end CFSG.KC.S63K

end
