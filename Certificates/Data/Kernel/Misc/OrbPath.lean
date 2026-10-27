module

public import Certificates.Data.Kernel.Misc.WordPts

public section

namespace CFSG.KC.OrbPath

open CFSG.KLie.CT CFSG.KC.WordPts
open CFSG.KC.Enum (strictN)

@[expose] noncomputable def digP (n w : Nat) (H : Nat → Nat) (d x : Nat) : Nat :=
  nIf(Nat.beq d (nat_lit 0), x, imgP n w (H (Nat.sub d (nat_lit 1))) x)

@[expose] noncomputable def pathAp (n w : Nat) (H : Nat → Nat) (f P x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih P x => strictN (ih (Nat.shiftRight P (nat_lit 2)) x) fun y =>
      digP n w H (Nat.land P (nat_lit 3)) y) f P x

@[expose] noncomputable def pathApI (n w : Nat) (HI : Nat → Nat) (f P x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih P x => strictN (digP n w HI (Nat.land P (nat_lit 3)) x) fun y =>
      ih (Nat.shiftRight P (nat_lit 2)) y) f P x

@[expose] noncomputable def keyK (n w : Nat) (G GI H HI : Nat → Nat) (f b : Nat)
    (T : List (List Int)) (P : Nat) : Nat :=
  strictN (pathApI n w HI f P b) fun y =>
    List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
      (fun t _ ih i => Nat.lor (Nat.shiftLeft (pathAp n w H f P (evW n w G GI t y)) (Nat.mul w i))
        (ih (Nat.succ i))) T (nat_lit 0)

@[expose] noncomputable def recAt (rw lb : Nat) (CF : Nat → Nat) (k : Nat) : Nat :=
  fget (CF (Nat.shiftRight k lb)) (Nat.land k (maskN lb)) rw

@[expose] noncomputable def orbRecK (n w : Nat) (G GI H HI : Nat → Nat) (f b : Nat)
    (T : List (List Int)) (rw lb : Nat) (CF : Nat → Nat) (N k : Nat) : Bool :=
  CFSG.KC.M1F2.strictB (Nat.mul w T.length) fun kw =>
  CFSG.KC.M1F2.strictB (recAt rw lb CF k) fun r =>
  CFSG.KC.M1F2.strictB (Nat.land r (maskN kw)) fun key =>
    andB (Nat.beq (keyK n w G GI H HI f b T (Nat.shiftRight r kw)) key)
      (bIf(Nat.blt (Nat.succ k) N,
        Nat.blt key (Nat.land (recAt rw lb CF (Nat.succ k)) (maskN kw)), true))

end CFSG.KC.OrbPath

end
