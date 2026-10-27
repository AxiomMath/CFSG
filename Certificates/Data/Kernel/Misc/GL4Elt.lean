module

public import Certificates.Data.Kernel.Misc.GL4Code

public section

namespace CFSG.KC.Misc.GL4

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def lAt (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih j => Nat.rec (motive := fun _ => Nat) x (fun j' _ => ih j') j) l i

@[expose] noncomputable def lAtL (L : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih j => Nat.rec (motive := fun _ => List Nat) x (fun j' _ => ih j') j) L i

@[expose] noncomputable def pow4F (c n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) id4 (fun _ acc => mul4F acc c) n

@[expose] noncomputable def inv4F (c : Nat) : Nat := pow4F c (nat_lit 419)

@[expose] noncomputable def invOK (c : Nat) : Bool :=
  andB (Nat.blt c (nat_lit 65536)) (Nat.beq (mul4F c (inv4F c)) id4)

@[expose] noncomputable def normOK (H : List Nat) (s : Nat) : Bool :=
  andB (invOK s) (CFSG.KC.LQT.P.letB (inv4F s) fun si =>
    allL H fun h => CFSG.KC.Misc.memN (mul4F (mul4F s h) si) H)

@[expose] noncomputable def inL (E : Nat → Nat) (N c : Nat) : Bool :=
  anyN N fun k => Nat.beq (E k) c

@[expose] noncomputable def bsStep (E SG : Nat → Nat) (c s : Nat) : Nat :=
  CFSG.KC.Misc.letN (Nat.mod s (nat_lit 65536)) fun lo =>
    CFSG.KC.Misc.letN (Nat.shiftRight s (nat_lit 16)) fun hi =>
      Bool.rec (motive := fun _ => Nat) s
        (CFSG.KC.Misc.letN (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)) fun m =>
          Bool.rec (motive := fun _ => Nat) (Nat.add lo (Nat.shiftLeft m (nat_lit 16)))
            (Nat.add (Nat.succ m) (Nat.shiftLeft hi (nat_lit 16))) (Nat.blt (E (SG m)) c))
        (Nat.blt lo hi)

@[expose] noncomputable def posK (E SG : Nat → Nat) (N c : Nat) : Nat :=
  Nat.mod (Nat.rec (motive := fun _ => Nat) (Nat.shiftLeft N (nat_lit 16))
    (fun _ s => bsStep E SG c s) (nat_lit 16)) (nat_lit 65536)

@[expose] noncomputable def brK (E SG : Nat → Nat) (N c q : Nat) : Bool :=
  andB (Nat.ble q N) (andB (orB (Nat.beq q (nat_lit 0)) (Nat.blt (E (SG (Nat.pred q))) c))
    (orB (Nat.beq q N) (Nat.blt c (E (SG q)))))

@[expose] noncomputable def outK (E SG : Nat → Nat) (N c : Nat) : Bool :=
  letB (posK E SG N c) fun q => brK E SG N c q

@[expose] noncomputable def colC (u : Nat) : Nat :=
  Nat.add (Nat.add (Nat.land u (nat_lit 1)) (Nat.mul (Nat.land (Nat.shiftRight u (nat_lit 1))
    (nat_lit 1)) (nat_lit 16))) (Nat.add (Nat.mul (Nat.land (Nat.shiftRight u (nat_lit 2))
    (nat_lit 1)) (nat_lit 256)) (Nat.mul (Nat.land (Nat.shiftRight u (nat_lit 3)) (nat_lit 1))
    (nat_lit 4096)))

@[expose] noncomputable def cntN (m : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (f i)) m

@[expose] noncomputable def fixFree (c : Nat) : Bool :=
  allN (nat_lit 15) fun u => notB (Nat.beq (mul4F c (colC (Nat.succ u))) (colC (Nat.succ u)))

@[expose] noncomputable def fixCnt (c : Nat) : Nat :=
  cntN (nat_lit 16) fun u => Nat.beq (mul4F c (colC u)) (colC u)

@[expose] noncomputable def ordDiv (c n : Nat) : Bool :=
  andB (notB (Nat.beq c id4)) (Nat.beq (pow4F c n) id4)

@[expose] noncomputable def conjW (E : Nat → Nat) (N c w : Nat) : Bool :=
  letB (Nat.mod w (nat_lit 512)) fun l => letB (Nat.shiftRight w (nat_lit 9)) fun li =>
    andB (Nat.blt l N) (andB (Nat.blt li N) (andB (Nat.beq (mul4F (E l) (E li)) id4)
      (notB (Nat.beq (pow4F (mul4F c (mul4F (mul4F (E l) c) (E li))) (nat_lit 8)) id4))))

end CFSG.KC.Misc.GL4

end
