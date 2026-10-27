module

public import CFSG.Certificates.Kernel.MonsterConv.PermValid
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.E7Orbit

open CFSG.KC.MonsterConv.Perm CFSG.KC.Enum

@[expose] noncomputable def band (a b : Bool) : Bool := Bool.rec false b a

@[expose] noncomputable def dg (c d : Nat) : Nat := Nat.mod (Nat.div c d) (nat_lit 3)

@[expose] noncomputable def pr (u c d e : Nat) : Nat := Nat.mul (dg u d) (dg c e)

@[expose] noncomputable def polS (u c : Nat) : Nat :=
  Nat.add (pr u c (nat_lit 1) (nat_lit 1)) (Nat.add (pr u c (nat_lit 3) (nat_lit 3))
  (Nat.add (pr u c (nat_lit 9) (nat_lit 9)) (Nat.add (pr u c (nat_lit 27) (nat_lit 27))
  (Nat.add (pr u c (nat_lit 81) (nat_lit 81)) (Nat.add (pr u c (nat_lit 243) (nat_lit 243))
  (Nat.add (pr u c (nat_lit 729) (nat_lit 729))
  (Nat.add (Nat.add (pr u c (nat_lit 1) (nat_lit 9)) (pr u c (nat_lit 9) (nat_lit 1)))
  (Nat.add (Nat.add (pr u c (nat_lit 3) (nat_lit 27)) (pr u c (nat_lit 27) (nat_lit 3)))
  (Nat.add (Nat.add (pr u c (nat_lit 9) (nat_lit 27)) (pr u c (nat_lit 27) (nat_lit 9)))
  (Nat.add (Nat.add (pr u c (nat_lit 27) (nat_lit 81)) (pr u c (nat_lit 81) (nat_lit 27)))
  (Nat.add (Nat.add (pr u c (nat_lit 81) (nat_lit 243)) (pr u c (nat_lit 243) (nat_lit 81)))
    (Nat.add (pr u c (nat_lit 243) (nat_lit 729)) (pr u c (nat_lit 729) (nat_lit 243))))))))))))))

@[expose] noncomputable def rxD (u c m d : Nat) : Nat :=
  Nat.mul (Nat.mod (Nat.add (dg c d) (Nat.mul m (dg u d))) (nat_lit 3)) d

@[expose] noncomputable def rxM (u c m : Nat) : Nat :=
  Nat.add (rxD u c m (nat_lit 1)) (Nat.add (rxD u c m (nat_lit 3))
    (Nat.add (rxD u c m (nat_lit 9)) (Nat.add (rxD u c m (nat_lit 27))
    (Nat.add (rxD u c m (nat_lit 81)) (Nat.add (rxD u c m (nat_lit 243))
      (rxD u c m (nat_lit 729)))))))

@[expose] noncomputable def rxN (u c : Nat) : Nat :=
  strictN (Nat.mul (nat_lit 2) (Nat.mod (Nat.mul (nat_lit 2) (polS u c)) (nat_lit 3)))
    (rxM u c)

@[expose] noncomputable def uP : Nat :=
  Nat.lor (nat_lit 194) (Nat.lor (Nat.shiftLeft (nat_lit 307) (nat_lit 12))
    (Nat.lor (Nat.shiftLeft (nat_lit 585) (nat_lit 24))
    (Nat.lor (Nat.shiftLeft (nat_lit 324) (nat_lit 36))
    (Nat.lor (Nat.shiftLeft (nat_lit 1216) (nat_lit 48))
      (Nat.shiftLeft (nat_lit 2135) (nat_lit 60))))))

@[expose] noncomputable def wP : Nat :=
  Nat.lor (nat_lit 324) (Nat.lor (Nat.shiftLeft (nat_lit 1216) (nat_lit 12))
    (Nat.lor (Nat.shiftLeft (nat_lit 2135) (nat_lit 24))
    (Nat.lor (Nat.shiftLeft (nat_lit 194) (nat_lit 36))
    (Nat.lor (Nat.shiftLeft (nat_lit 307) (nat_lit 48))
      (Nat.shiftLeft (nat_lit 585) (nat_lit 60))))))

@[expose] noncomputable def gF (k p : Nat) : Nat :=
  rxN (pg (nat_lit 12) (nat_lit 4095) uP k) (rxN (pg (nat_lit 12) (nat_lit 4095) wP k) p)

@[expose] noncomputable def hN (j p : Nat) : Nat :=
  rxN (nat_lit 1) (rxN (Nat.pow (nat_lit 3) (Nat.succ j)) p)

@[expose] noncomputable def packF (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.lor acc (Nat.shiftLeft (f c) (Nat.mul (nat_lit 12) c))) n

@[expose] noncomputable def hP (j : Nat) : Nat := packF (hN j) (nat_lit 2187)

@[expose] noncomputable def salt : Nat :=
  Nat.land (Nat.pow (nat_lit 3) (nat_lit 82713)) (ones (nat_lit 4096))

@[expose] noncomputable def img (N S : Nat) : Nat :=
  Nat.land (netApply (nat_lit 12) (nat_lit 4096) (repU (nat_lit 4096) (nat_lit 2)) N
    (Nat.lor S (Nat.shiftLeft salt (nat_lit 4096)))) (ones (nat_lit 4096))

@[expose] noncomputable def recAt (T : Nat → Nat) (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (T (Nat.shiftRight i (nat_lit 4)))
    (Nat.mul (nat_lit 2304) (Nat.land i (nat_lit 15)))) (ones (nat_lit 2304))

@[expose] noncomputable def msk (R : Nat) : Nat := Nat.land R (ones (nat_lit 2240))

@[expose] noncomputable def parF (R : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (nat_lit 2240)) (nat_lit 65535)

@[expose] noncomputable def letF (R : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (nat_lit 2256)) (nat_lit 255)

@[expose] noncomputable def depF (R : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (nat_lit 2264)) (nat_lit 255)

@[expose] noncomputable def blkF (R : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (nat_lit 2272)) (nat_lit 255)

@[expose] noncomputable def edgeOK (T NT : Nat → Nat) (R S b d : Nat) : Bool :=
  strictB (parF R) fun p => strictB (letF R) fun l => strictB (recAt T p) fun Q =>
    band (Nat.blt p (nat_lit 3159))
    (band (Nat.blt l (nat_lit 6))
    (band (Nat.beq (Nat.succ (depF Q)) d)
    (band (Nat.beq (blkF Q) b)
      (Nat.beq (img (NT l) (msk Q)) S))))

@[expose] noncomputable def nodeOK (T NT RT : Nat → Nat) (i : Nat) : Bool :=
  strictB (recAt T i) fun R => strictB (msk R) fun S => strictB (blkF R) fun b =>
  strictB (depF R) fun d =>
    band (Nat.beq (Nat.shiftRight S (nat_lit 2187)) (nat_lit 0))
    (band (Bool.rec (motive := fun _ => Bool) true
        (Nat.blt S (msk (recAt T (Nat.succ i))))
        (Nat.blt (Nat.succ i) (nat_lit 3159)))
    (band (Nat.blt b (nat_lit 4))
      (Bool.rec (motive := fun _ => Bool) (edgeOK T NT R S b d) (Nat.beq i (RT b))
        (Nat.beq d (nat_lit 0)))))

@[expose] noncomputable def chunkOK (T NT RT : Nat → Nat) (c : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 64) c)
    (fun i => Bool.rec (motive := fun _ => Bool) true (nodeOK T NT RT i)
      (Nat.blt i (nat_lit 3159)))
    (nat_lit 64)

@[expose] noncomputable def cnt (T : Nat → Nat) (n : Nat) : Nat :=
  foldN n (fun i acc => Nat.add acc
    (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 20) (blkF (recAt T i))))) (nat_lit 0)

@[expose] noncomputable def cntOK (T : Nat → Nat) : Bool :=
  Nat.beq (cnt T (nat_lit 3159))
    (Nat.add (nat_lit 1) (Nat.add (Nat.shiftLeft (nat_lit 288) (nat_lit 20))
      (Nat.add (Nat.shiftLeft (nat_lit 630) (nat_lit 40))
        (Nat.shiftLeft (nat_lit 2240) (nat_lit 60)))))

@[expose] noncomputable def ext (G p : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) p (pg (nat_lit 12) (nat_lit 4095) G p)
    (Nat.blt p (nat_lit 2187))

@[expose] noncomputable def plane (G b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p acc => Nat.lor acc (Nat.shiftLeft
      (Nat.land (Nat.shiftRight (ext G p) b) (nat_lit 1)) p)) (nat_lit 4096)

@[expose] noncomputable def planes (G : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft (plane G b) (Nat.mul b (nat_lit 4096))))
    (nat_lit 12)

@[expose] noncomputable def bindOK (NT : Nat → Nat) (G l : Nat) : Bool :=
  band (netValid (nat_lit 12) (NT l))
    (Nat.beq (netApply (nat_lit 12) (nat_lit 4096) (repU (nat_lit 4096) (nat_lit 12)) (NT l)
      (planes G)) (idP (nat_lit 12)))

@[expose] noncomputable def wordPt (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih w p => Bool.rec (motive := fun _ => Nat)
      (strictN (gF (Nat.sub (Nat.mod w (nat_lit 8)) (nat_lit 1)) p) (ih (Nat.div w (nat_lit 8))))
      p (Nat.beq w (nat_lit 0))) fuel

@[expose] noncomputable def wordMask (w : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) (wordPt (nat_lit 32) w p)) ih) L

end CFSG.KC.E7Orbit

end
