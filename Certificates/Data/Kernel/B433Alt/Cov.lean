module

public import Certificates.Data.Kernel.B433Alt.Link
public import Certificates.Data.Kernel.B433Alt.Struct

public section

namespace CFSG.KC.B4A

open CFSG.KC.Y333

@[expose] noncomputable def stShift (t : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) (Nat.sub t (nat_lit 19)))
    (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 19) t)) (Nat.blt t (nat_lit 20))

@[expose] noncomputable def netApp (MS : Nat → Nat) (c x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun t acc => sN acc (fun a => dsw (stShift t) (MS (Nat.add (Nat.mul (nat_lit 39) c) t)) a)) (nat_lit 39)

@[expose] noncomputable def appW (MS : Nat → Nat) (w E : Nat) : Nat :=
  sN (wLen w) (fun n =>
    Nat.rec (motive := fun _ => Nat) E
      (fun j acc => sN acc (fun a => netApp MS (wAt w (Nat.sub (Nat.sub n (nat_lit 1)) j)) a)) n)

@[expose] noncomputable def colAt (CB : Nat → Nat) (c x : Nat) : Nat :=
  sN (CB (Nat.add (Nat.mul (nat_lit 256) c) (Nat.shiftRight x (nat_lit 12)))) (fun B =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 1048576) (colGet B (colOff x)) (tagOK B x))

@[expose] noncomputable def walkId (CB : Nat → Nat) (w : Nat) : Nat :=
  sN (wLen w) (fun n =>
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => sN acc (fun x => colAt CB (wAt w (Nat.sub (Nat.sub n (nat_lit 1)) j)) x)) n)

@[expose] noncomputable def entryOK (RD : Nat → Nat) (LIVE j e : Nat) : Bool :=
  sB (RD e) (fun d => andB (isFact (dKind d)) (andB (Nat.beq (dN1 d) j)
    (Nat.blt (nat_lit 0) (Nat.land LIVE (Nat.shiftLeft (nat_lit 1) (dN2 d))))))

@[expose] noncomputable def rootSet (RD PW CB : Nat → Nat) (LIVE j n L : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih L acc => sN (Nat.land L (ones (nat_lit 20))) (fun e =>
      Bool.rec (motive := fun _ => Nat) (nat_lit 0)
        (sN (Nat.lor acc (Nat.shiftLeft (nat_lit 1) (walkId CB (PW (dPt (RD e)))))) (fun a =>
          ih (Nat.shiftRight L (nat_lit 20)) a))
        (entryOK RD LIVE j e)))
    n L (nat_lit 0)

@[expose] noncomputable def genOK (RD : Nat → Nat) (j g : Nat) : Bool :=
  sB (RD g) (fun d => andB (isStab (dKind d)) (Nat.beq (dN2 d) j))

@[expose] noncomputable def stepOK (RD RW MS : Nat → Nat) (j g E E' : Nat) : Bool :=
  andB (genOK RD j g) (Nat.beq (Nat.lor E (appW MS (RW g) E)) E')

@[expose] noncomputable def appSeg (MS : Nat → Nat) (w a n X : Nat) : Nat :=
  sN (wLen w) (fun len =>
    Nat.rec (motive := fun _ => Nat) X
      (fun j acc => sN acc (fun x => netApp MS (wAt w (Nat.sub (Nat.sub len (nat_lit 1)) (Nat.add a j))) x)) n)

@[expose] noncomputable def segOK (RD RW MS : Nat → Nat) (j g a n X X' : Nat) : Bool :=
  andB (genOK RD j g) (andB (Nat.ble (Nat.add a n) (wLen (RW g))) (Nat.beq (appSeg MS (RW g) a n X) X'))

@[expose] noncomputable def segEnd (RW : Nat → Nat) (g a E X E' : Nat) : Bool :=
  andB (Nat.beq a (wLen (RW g))) (Nat.beq (Nat.lor E X) E')

end CFSG.KC.B4A

end
