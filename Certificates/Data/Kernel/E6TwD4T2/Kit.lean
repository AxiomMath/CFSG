module

public section

namespace CFSG.KD.E6TwD4T2

@[expose] noncomputable def full : Nat := Nat.sub (Nat.shiftLeft 1 729) 1

@[expose] noncomputable def pl (j a : Nat) : Nat :=
  Nat.mul (Nat.div full (Nat.sub (Nat.shiftLeft 1 (Nat.pow 3 (Nat.succ j))) 1))
    (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 (Nat.pow 3 j)) 1) (Nat.mul a (Nat.pow 3 j)))

@[expose] noncomputable def get (S s : Nat) : Nat := Nat.land (Nat.shiftRight S (Nat.mul s 729)) full

@[expose] noncomputable def pack (a b c : Nat) : Nat :=
  Nat.lor a (Nat.lor (Nat.shiftLeft b 729) (Nat.shiftLeft c 1458))

@[expose] noncomputable def bit (m k : Nat) : Bool := Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 k))

@[expose] noncomputable def or3 (a b c : Nat) : Nat := Nat.lor a (Nat.lor b c)

@[expose] noncomputable def st1 (A0 A1 A2 P0 P1 P2 : Nat) : Nat :=
  pack (or3 (Nat.land A0 P0) (Nat.land A2 P1) (Nat.land A1 P2))
    (or3 (Nat.land A1 P0) (Nat.land A0 P1) (Nat.land A2 P2))
    (or3 (Nat.land A2 P0) (Nat.land A1 P1) (Nat.land A0 P2))

@[expose] noncomputable def st2 (A0 A1 A2 P0 P1 P2 : Nat) : Nat :=
  pack (or3 (Nat.land A0 P0) (Nat.land A1 P1) (Nat.land A2 P2))
    (or3 (Nat.land A1 P0) (Nat.land A2 P1) (Nat.land A0 P2))
    (or3 (Nat.land A2 P0) (Nat.land A0 P1) (Nat.land A1 P2))

@[expose] noncomputable def stepL (j x S : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (st2 (get S 0) (get S 1) (get S 2) (pl j 0) (pl j 1) (pl j 2))
      (st1 (get S 0) (get S 1) (get S 2) (pl j 0) (pl j 1) (pl j 2)) (Nat.beq x 1))
    S (Nat.beq x 0)

@[expose] noncomputable def lvl (v : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun x _ ih j S => ih (Nat.succ j) (stepL j x S)) v 0 full

@[expose] noncomputable def lv (S k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) 0 2 (bit (get S 2) k)) 1 (bit (get S 1) k)

@[expose] noncomputable def neg3 (s : Nat) : Nat := Nat.mod (Nat.sub 3 s) 3

@[expose] noncomputable def wv (r3 : List (List Nat)) (t : List Nat) : List (List Nat) :=
  (List.range 6).map fun j => (List.range 6).map fun i =>
    ((r3.getD (t.getD j 0) []).getD i 0 + (if i == j then 2 else 0)) % 3

@[expose] noncomputable def tpm (M : List Nat) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) full (fun S _ ih => Nat.land ih (get S (neg3 (lv S k)))) M

@[expose] noncomputable def tmm (M : List Nat) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) full (fun S _ ih => Nat.land ih (get S (lv S k))) M

@[expose] noncomputable def allz (M : List Nat) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun S _ ih => Bool.and ih (Nat.beq (lv S k) 0)) M

@[expose] noncomputable def rmask (sigL : List Nat) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun L _ ih => Bool.rec (motive := fun _ => Nat) ih (Nat.lor ih L) (bit L k)) sigL

@[expose] noncomputable def condK (wlv : List (List Nat)) (sigL : List Nat) (G k : Nat) : Bool :=
  Bool.or (List.rec (motive := fun _ => Bool) false (fun M _ ih => Bool.or ih (allz M k)) wlv)
    (Nat.beq (Nat.lor (Nat.lor (rmask sigL k) G)
      (List.rec (motive := fun _ => Nat) 0
        (fun M _ ih => Nat.lor ih (Nat.lor (tpm M k) (tmm M k))) wlv)) full)

@[expose] noncomputable def pairsK (wlv : List (List Nat)) (sigL : List Nat) (G n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.and ih (condK wlv sigL G k)) n

@[expose] noncomputable def fixM (r3 : List (List Nat)) (t : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) full (fun w _ ih => Nat.land ih (get (lvl w) 0)) (wv r3 t)

@[expose] noncomputable def badM (r3 : List (List Nat)) (t negs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (fixM r3 t)
    (fun p _ ih => Nat.land ih (Nat.sub full (get (lvl (r3.getD p [])) 0))) negs

@[expose] noncomputable def stabK (r3 : List (List Nat)) (elems negs : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => Bool.and ih (Bool.or (e.1 == [0, 1, 2, 3, 4, 5]) (Nat.beq (badM r3 e.1 e.2) 0)))
    (elems.zip negs)

@[expose] noncomputable def beqB (b₁ b₂ : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (!b₂) b₂ b₁

@[expose] noncomputable def planesOK : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => Bool.and ih
    (Nat.rec (motive := fun _ => Bool) true (fun a ih2 => Bool.and ih2
      (Bool.and (Nat.blt (pl j a) (Nat.shiftLeft 1 729))
        (Nat.rec (motive := fun _ => Bool) true (fun k ih3 => Bool.and ih3
          (beqB (bit (pl j a) k) (Nat.beq (Nat.mod (Nat.div k (Nat.pow 3 j)) 3) a))) 729))) 3)) 6

@[expose] noncomputable def r3OK (r3 : List (List Nat)) : Bool :=
  Nat.beq r3.length 72 && r3.all fun r => Nat.beq r.length 6 && r.all fun x => Nat.blt x 3

@[expose] noncomputable def tabOK (r3 wts wlv : List (List Nat)) : Bool :=
  ((wts.map (wv r3)).map fun M => M.map lvl) == wlv

@[expose] noncomputable def sigOK (r3 : List (List Nat)) (sig sigL : List Nat) : Bool :=
  (sig.map fun p => get (lvl (r3.getD p [])) 0) == sigL

@[expose] noncomputable def gOf (wlv : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun M _ ih => Nat.lor ih (List.rec (motive := fun _ => Nat) full
      (fun S _ ih2 => Nat.land ih2 (get S 0)) M)) wlv

@[expose] noncomputable def gOK (wlv : List (List Nat)) (G : Nat) : Bool := Nat.beq (gOf wlv) G

end CFSG.KD.E6TwD4T2
