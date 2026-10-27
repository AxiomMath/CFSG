module

public import Certificates.Data.Kernel.EaLat

public section

namespace CFSG.KC.EaLat

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def full2048 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2048)) (nat_lit 1)

@[expose] noncomputable def planeK (l : Nat) : Nat :=
  letN (Nat.shiftLeft (nat_lit 1) l) fun b =>
    Nat.mul (Nat.shiftLeft (Nat.sub (Nat.shiftLeft (nat_lit 1) b) (nat_lit 1)) b)
      (Nat.div full2048 (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add b b)) (nat_lit 1)))

@[expose] noncomputable def lowK (l : Nat) : Nat :=
  letN (Nat.shiftLeft (nat_lit 1) l) fun b =>
    Nat.mul (Nat.sub (Nat.shiftLeft (nat_lit 1) b) (nat_lit 1))
      (Nat.div full2048 (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add b b)) (nat_lit 1)))

@[expose] noncomputable def colK (M c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (planeK j))
      (bit (fld M (Nat.mul (nat_lit 11) j) (nat_lit 2047)) c)) (nat_lit 11)

@[expose] noncomputable def fixK (M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) full2048
    (fun c acc => Nat.land acc (Nat.xor full2048 (Nat.xor (colK M c) (planeK c)))) (nat_lit 11)

@[expose] noncomputable def popK (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun l acc => letN acc fun y => letN (lowK l) fun m => Nat.add (Nat.land y m)
      (Nat.land (Nat.shiftRight y (Nat.shiftLeft (nat_lit 1) l)) m)) (nat_lit 11)

@[expose] noncomputable def fxAt (FX V : Nat → Nat) (i : Nat) : Bool := Nat.beq (FX i) (fixK (V i))

@[expose] noncomputable def fvAt (FV FX REC : Nat → Nat) (f : Nat) : Bool :=
  letB (REC f) fun r => letB (FV f) fun v =>
    Bool.rec (motive := fun _ => Bool)
      (andB (Nat.beq v (Nat.land (FV (fld r (nat_lit 0) (nat_lit 65535)))
          (FX (fld r (nat_lit 16) (nat_lit 255)))))
        (Nat.ble (Nat.mul (popK v) (Nat.succ (fld r (nat_lit 24) (nat_lit 255)))) (nat_lit 1024)))
      (Nat.beq v full2048) (Nat.beq f (nat_lit 0))

end CFSG.KC.EaLat

end
