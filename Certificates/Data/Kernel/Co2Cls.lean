module

public import Certificates.Data.Kernel.Co2Syl
public import CFSG.Certificates.Kernel.BabyMonster.Native.Q23

public section

namespace CFSG.KC.Co2Cls

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2Syl

@[expose] noncomputable def recC (CF G : Nat → Nat) (NG X0 N k : Nat) : Bool :=
  letB (recAt CF k) fun r => letB (elemOf r) fun X =>
    andK (sortK CF N k (sOf r))
      (bIf(Nat.beq k (nat_lit 0), Nat.beq X X0,
        letB (tOf r (nat_lit 0)) fun p => letB (tOf r (nat_lit 1)) fun j =>
          andK (Nat.blt p k) (andK (Nat.blt j NG)
            (Nat.beq (mulV X (G j)) (mulV (G j) (elemAt CF p))))))

@[expose] noncomputable def oixOf (q l : Nat) : Nat :=
  fld(q, Nat.mul (nat_lit 8) l, nat_lit 255)

@[expose] noncomputable def oEdge (O H : Nat → Nat) (m X l b : Nat) : Bool :=
  andK (Nat.blt b m) (Nat.beq (mulV (O b) (H l)) (mulV (H l) X))

@[expose] noncomputable def orbK (O IX H : Nat → Nat) (h m a : Nat) : Bool :=
  letB (O a) fun X => letB (IX a) fun q =>
    Nat.rec (motive := fun _ => Bool) true
      (fun l acc => andK (oEdge O H m X l (oixOf q l)) acc) h

@[expose] noncomputable def powK (W e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) IDP (fun _ acc => mulV acc W) e

@[expose] noncomputable def ordK (W p : Nat) : Bool :=
  andK (Nat.beq (powK W p) IDP) (notK (Nat.beq W IDP))

@[expose] noncomputable def oddW (Y W p : Nat) : Bool := andK (ordK W p) (commK W Y)

@[expose] noncomputable def pairW (Y U V : Nat) : Bool :=
  andK (oddW Y U (nat_lit 3)) (andK (oddW Y V (nat_lit 3)) (andK (commK U V)
    (andK (notK (Nat.beq V U)) (notK (Nat.beq V (mulV U U))))))

@[expose] noncomputable def ech22L (fromK : Bool) (Q k : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ st => st)
    (fun _ ih R i st => CFSG.KC.BM.forceB
      ((fun r => Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) st (CFSG.KC.BM.echStep r st) (Nat.ble k i))
          (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) st
              (Nat.beq r (nat_lit 0)))
            (CFSG.KC.BM.echStep r st) (Nat.blt i k))
          (CFSG.KC.BM.notB fromK))
        (Nat.land R (nat_lit 4194303)))
      (fun st' => ih (Nat.shiftRight R (nat_lit 22)) (Nat.succ i) st'))
    (nat_lit 22) Q (nat_lit 0) (Nat.shiftLeft (nat_lit 1) (nat_lit 40)))

@[expose] noncomputable def rankL (M P Q k : Nat) : Bool :=
  andK (Nat.beq (mulV P M) Q) (andK (ech22L false Q k) (ech22L true P k))

end CFSG.KC.Co2Cls

end
