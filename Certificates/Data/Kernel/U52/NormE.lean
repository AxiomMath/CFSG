module

public import Certificates.Data.Kernel.U52.Norm

public section

namespace CFSG.KS.U52N

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def khG (KL : List Nat) : List Nat :=
  [KL.getD 1 0, KL.getD 3 0, KL.getD 9 0]

@[expose] noncomputable def khOK (n w m idn : Nat) (KL nK : List Nat) : Bool :=
  (Nat.beq KL.length 18 && memN idn KL &&
    KL.all (fun e => (khG KL).all (fun g => memN (pcomp n w m e g) KL))) &&
    (allN 9 (fun i => Nat.beq (KL.getD i 0) (nK.getD i 0) &&
      Nat.beq (KL.getD (i + 9) 0) (pcomp n w m (KL.getD 9 0) (nK.getD i 0))) &&
      KL.all (fun e => memN (pcomp n w m e e) nK))

@[expose] noncomputable def hatT (n w m fix : Nat) (KL ris : List Nat) (e : Nat) : Bool :=
  Nat.beq (pg w m e fix) fix || !memN (pcomp n w m e e) KL ||
    ris.any (fun r => memN (pcomp n w m r e) KL) ||
    !(khG KL).all (fun g => KL.any (fun c => Nat.beq (pcomp n w m e g) (pcomp n w m c e)))

@[expose] noncomputable def hatB (n w m idn : Nat) (nK S0 : List Nat) (e k : Nat)
    (sw : List Nat) : Bool :=
  !memN (pcomp n w m e e) nK || memN e nK ||
    (Nat.beq (pcomp n w m e (nK.getD k 0)) (evP n w m idn (fun c => S0.getD c 0) sw) &&
      !Nat.beq (pcomp n w m e (nK.getD k 0)) idn &&
      (Nat.blt k nK.length && sw.all (fun c => Nat.blt c S0.length)))

@[expose] noncomputable def hatF (n w m : Nat) (nK : List Nat) (C : List (List Nat)) (e : Nat) :
    Bool :=
  !memN (pcomp n w m e e) nK || C.any (fun c => memN e c)

end CFSG.KS.U52N

end
