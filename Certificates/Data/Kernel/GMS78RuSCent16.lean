module

public import Certificates.Data.Kernel.GMS78RuSCent

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def cDTest16 (DM pd ud : Nat) : Bool :=
  Nat.beq (Nat.shiftRight (fget DM (Nat.add (Nat.mul 8 pd) ud) 3) 1)
    (Nat.shiftRight (fget DM (Nat.add (Nat.mul 8 ud) pd) 3) 1)

@[expose] noncomputable def sCentE16 (m : Nat → Nat → Nat) (DPR : List Nat) (DM u i : Nat)
    (acc : List Nat) : List Nat :=
  (fun uc ud pd => Bool.rec (motive := fun _ => List Nat) acc
    ((fun L => (fun b => sCentT m u b L (sCentT m u (Nat.add b 256) L acc)) (Nat.mul 512 i))
      (sFilter 256 fun pc => cCTest (neGet 0 DPR pd) (neGet 0 DPR ud) uc pc))
    (cDTest16 DM pd ud))
  (Nat.land u 255) (fget (nat_lit 3864) (Nat.shiftRight u 9) 3) (fget (nat_lit 3864) i 3)

@[expose] noncomputable def sCent16 (m : Nat → Nat → Nat) (DPR : List Nat) (DM u : Nat) :
    List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun i _ ih => sCentE16 m DPR DM u i ih) [0, 1, 2, 3]

@[expose] noncomputable def kKey16 (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO u k : Nat) :
    Bool :=
  neStrictB u fun u => neStrictB k fun k =>
  (fun m => Nat.beq (sKeyL m u (sCent16 m DPR DM u)) (kKeyPart k)) (mul16K GT DPR LIN DM DO)

end CFSG.KC.GMS

end
