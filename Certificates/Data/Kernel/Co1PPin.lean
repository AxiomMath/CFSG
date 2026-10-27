module

public import Certificates.Data.Kernel.Co1P

public section

namespace CFSG.KC.Co1P

open CFSG.KC.Loop CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KLie.CT

@[expose] noncomputable def tabK (w : Nat) (C : List Nat) (i : Nat) : Nat :=
  fget (getL (nat_lit 0) C (Nat.div i (nat_lit 64))) (Nat.mod i (nat_lit 64)) w

@[expose] noncomputable def recsEqK (R : Nat → Nat) : List (Nat × Nat) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih i => CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq r.1 (Nat.div (R i) (nat_lit 8)))
      (Nat.beq r.2 (Nat.mod (R i) (nat_lit 8)))) (ih (Nat.succ i)))

@[expose] noncomputable def pinAt (act : Nat → Nat → Nat) (root : Nat) (T R : Nat → Nat) (i : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) (Nat.beq (T (nat_lit 0)) root)
    (fun j _ => Nat.beq (T (Nat.succ j)) (act (Nat.mod (R j) (nat_lit 8)) (T (Nat.div (R j) (nat_lit 8))))) i

@[expose] noncomputable def pinChunk (act : Nat → Nat → Nat) (root : Nat) (T R : Nat → Nat) (N c : Nat) :
    Bool :=
  allN (nat_lit 64) fun k => (fun i => CFSG.KLie.CT.orB (Nat.ble N i) (pinAt act root T R i))
    (Nat.add (Nat.mul (nat_lit 64) c) k)

@[expose] noncomputable def lowK (kw X : Nat) : Nat := Nat.mod X (Nat.shiftLeft (nat_lit 1) kw)

@[expose] noncomputable def keyAt (N kw : Nat) (SK IX P : Nat → Nat) (s : Nat) : Bool :=
  CFSG.KLie.CT.andB (CFSG.KLie.CT.orB (Nat.ble N (Nat.succ s)) (Nat.blt (SK s) (SK (Nat.succ s))))
    (CFSG.KLie.CT.andB (Nat.blt (IX s) N) (Nat.beq (SK s) (lowK kw (P (IX s)))))

@[expose] noncomputable def keyChunk (N kw : Nat) (SK IX P : Nat → Nat) (c : Nat) : Bool :=
  allN (nat_lit 64) fun k => (fun s => CFSG.KLie.CT.orB (Nat.ble N s) (keyAt N kw SK IX P s))
    (Nat.add (Nat.mul (nat_lit 64) c) k)

@[expose] noncomputable def bsK (SK : Nat → Nat) (x : Nat) (d : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
    (fun _ ih lo hi => Bool.rec (motive := fun _ => Nat) lo
      ((fun m => Bool.rec (motive := fun _ => Nat) (ih lo m) (ih (Nat.succ m) hi) (Nat.blt (SK m) x))
        (Nat.div (Nat.add lo hi) (nat_lit 2))) (Nat.blt lo hi)) d

@[expose] noncomputable def memPin (N kw d : Nat) (SK IX P : Nat → Nat) (X : Nat) : Bool :=
  (fun s => CFSG.KLie.CT.andB (Nat.blt s N) (CFSG.KLie.CT.andB (Nat.beq (SK s) (lowK kw X)) (eqK X (P (IX s)))))
    (bsK SK (lowK kw X) d (nat_lit 0) N)

end CFSG.KC.Co1P

end
