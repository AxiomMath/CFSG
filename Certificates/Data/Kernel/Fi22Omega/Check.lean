module

public import CFSG.Certificates.Kernel.MonsterConv.PermValid
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Fi22Omega

open CFSG.KC.MonsterConv.Perm CFSG.KC.Enum

@[expose] noncomputable def band (a b : Bool) : Bool := Bool.rec false b a

@[expose] noncomputable def salt : Nat :=
  Nat.land (Nat.pow (nat_lit 3) (nat_lit 82713)) (ones (nat_lit 4096))

@[expose] noncomputable def img (N S : Nat) : Nat :=
  Nat.land (netApply (nat_lit 12) (nat_lit 4096) (repU (nat_lit 4096) (nat_lit 2)) N
    (Nat.lor S (Nat.shiftLeft salt (nat_lit 4096)))) (ones (nat_lit 4096))

@[expose] noncomputable def recAt (T : Nat → Nat) (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (T (Nat.shiftRight i (nat_lit 4)))
    (Nat.mul (nat_lit 3584) (Nat.land i (nat_lit 15)))) (ones (nat_lit 3584))

@[expose] noncomputable def msk (R : Nat) : Nat := Nat.land R (ones (nat_lit 3520))

@[expose] noncomputable def parF (R : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (nat_lit 3520)) (nat_lit 65535)

@[expose] noncomputable def letF (R : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (nat_lit 3536)) (nat_lit 255)

@[expose] noncomputable def depF (R : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (nat_lit 3544)) (nat_lit 255)

@[expose] noncomputable def blkF (R : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (nat_lit 3552)) (nat_lit 255)

@[expose] noncomputable def key (S : Nat) : Nat := Nat.land S (ones (nat_lit 192))

@[expose] noncomputable def edgeOK (T NT : Nat → Nat) (R S b d : Nat) : Bool :=
  strictB (parF R) fun p => strictB (letF R) fun l => strictB (recAt T p) fun Q =>
    band (Nat.blt p (nat_lit 61776))
    (band (Nat.blt l (nat_lit 2))
    (band (Nat.beq (Nat.succ (depF Q)) d)
    (band (Nat.beq (blkF Q) b)
      (Nat.beq (img (NT l) (msk Q)) S))))

@[expose] noncomputable def nodeOK (T NT RT : Nat → Nat) (i : Nat) : Bool :=
  strictB (recAt T i) fun R => strictB (msk R) fun S => strictB (blkF R) fun b =>
  strictB (depF R) fun d =>
    band (Nat.beq (Nat.shiftRight S (nat_lit 3510)) (nat_lit 0))
    (band (Bool.rec (motive := fun _ => Bool) true
        (Nat.blt (key S) (key (msk (recAt T (Nat.succ i)))))
        (Nat.blt (Nat.succ i) (nat_lit 61776)))
    (band (Nat.blt b (nat_lit 4))
      (Bool.rec (motive := fun _ => Bool) (edgeOK T NT R S b d) (Nat.beq i (RT b))
        (Nat.beq d (nat_lit 0)))))

@[expose] noncomputable def chunkOK (T NT RT : Nat → Nat) (c : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 64) c)
    (fun i => Bool.rec (motive := fun _ => Bool) true (nodeOK T NT RT i)
      (Nat.blt i (nat_lit 61776)))
    (nat_lit 64)

@[expose] noncomputable def cnt (T : Nat → Nat) (n : Nat) : Nat :=
  foldN n (fun i acc => Nat.add acc
    (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 20) (blkF (recAt T i))))) (nat_lit 0)

@[expose] noncomputable def cntOK (T : Nat → Nat) : Bool :=
  Nat.beq (cnt T (nat_lit 61776))
    (Nat.add (nat_lit 1) (Nat.add (Nat.shiftLeft (nat_lit 37800) (nat_lit 20))
      (Nat.add (Nat.shiftLeft (nat_lit 22400) (nat_lit 40))
        (Nat.shiftLeft (nat_lit 1575) (nat_lit 60)))))

@[expose] noncomputable def ext (G p : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) p (pg (nat_lit 12) (nat_lit 4095) G p)
    (Nat.blt p (nat_lit 3510))

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

@[expose] noncomputable def wordPt (A : Nat → Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih w p => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.div w (nat_lit 8))
        (pg (nat_lit 12) (nat_lit 4095) (A (Nat.sub (Nat.mod w (nat_lit 8)) (nat_lit 1))) p))
      p (Nat.beq w (nat_lit 0))) fuel

@[expose] noncomputable def wordMask (A : Nat → Nat) (w : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) (wordPt A (nat_lit 128) w p)) ih) L

@[expose] noncomputable def mapsOK (A : Nat → Nat) (w : Nat) (L : List Nat) (M M' : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => band
      (Bool.rec (motive := fun _ => Bool) true
        (Nat.testBit M' (wordPt A (nat_lit 128) w p)) (Nat.testBit M p)) ih) L

end CFSG.KC.Fi22Omega

end
