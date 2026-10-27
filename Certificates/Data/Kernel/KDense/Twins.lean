module

public import Certificates.Data.Kernel.KDense.Letters

public section

namespace CFSG.KC.KDense

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] noncomputable def BMS : Nat :=
  nat_lit 0xaaaa00cccc00c6a0a06ac0c06ca00aa6c00ce111111e111111e111111e111111e111111e

@[expose] noncomputable def UMS : Nat :=
  nat_lit 0x30f00050f00003f00005f00000c00000a01111101000f00100f00010f00001f00000e

@[expose] noncomputable def bmT (i : Nat) : Nat := fld(BMS, Nat.mul (nat_lit 24) i, nat_lit 16777215)

@[expose] noncomputable def umT (k : Nat) : Nat := fld(UMS, Nat.mul (nat_lit 24) k, nat_lit 16777215)

@[expose] noncomputable def popcT (k a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => Nat.add acc (bitN a i)) k

@[expose] noncomputable def parT (k a : Nat) : Nat := Nat.land (popcT k a) (nat_lit 1)

@[expose] noncomputable def popc24 (a : Nat) : Nat :=
  (fun x => (fun y => (fun z => Nat.add (Nat.add (Nat.land z (nat_lit 255)) (Nat.land (Nat.shiftRight z (nat_lit 8))
      (nat_lit 255))) (Nat.shiftRight z (nat_lit 16)))
      (Nat.land (Nat.add y (Nat.shiftRight y (nat_lit 4))) (nat_lit 0x0f0f0f)))
    (Nat.add (Nat.land x (nat_lit 0x333333)) (Nat.land (Nat.shiftRight x (nat_lit 2)) (nat_lit 0x333333))))
  ((fun a' => Nat.sub a' (Nat.land (Nat.shiftRight a' (nat_lit 1)) (nat_lit 0x555555))) (Nat.land a (nat_lit 16777215)))

@[expose] noncomputable def par24 (a : Nat) : Nat :=
  (fun x => (fun y => (fun z => (fun u => (fun v => Nat.land (Nat.xor v (Nat.shiftRight v (nat_lit 1))) (nat_lit 1))
      (Nat.xor u (Nat.shiftRight u (nat_lit 2)))) (Nat.xor z (Nat.shiftRight z (nat_lit 4))))
      (Nat.xor y (Nat.shiftRight y (nat_lit 8)))) (Nat.xor x (Nat.shiftRight x (nat_lit 16))))
  (Nat.land a (nat_lit 16777215))

@[expose] noncomputable def combT (TB w n a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (selB (bitN a i) (fld(TB, Nat.mul w i, ones w)))) n

@[expose] noncomputable def wordT (a : Nat) : Nat := combT BMS (nat_lit 24) (nat_lit 12) a

@[expose] noncomputable def repT (d : Nat) : Nat := combT UMS (nat_lit 24) (nat_lit 12) d

@[expose] noncomputable def coeffT (w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (par24 (Nat.land w (umT k))) k)) (nat_lit 12)

@[expose] noncomputable def dualT (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.lor acc (Nat.shiftLeft (par24 (Nat.land v (bmT j))) j)) (nat_lit 12)

@[expose] noncomputable def pairT (a d : Nat) : Nat := par24 (Nat.land (Nat.land a d) (nat_lit 4095))

@[expose] noncomputable def betaT (j k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Nat.land (Nat.shiftRight (popc24 (Nat.land (bmT j) (bmT k))) (nat_lit 1)) (nat_lit 1))
      (Nat.land (Nat.shiftRight (popc24 (bmT j)) (nat_lit 2)) (nat_lit 1)) (Nat.beq j k))
    (nat_lit 0) (Nat.blt j k)

@[expose] noncomputable def packBetaT (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (betaT n k) k)) (nat_lit 12)

@[expose] noncomputable def thetaT (a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun n acc => Nat.xor acc (selB (bitN a n)
      (Nat.xor (packBetaT n) (dualT (Nat.land (combT BMS (nat_lit 24) n a) (bmT n)))))) (nat_lit 12)

@[expose] noncomputable def pT (a : Nat) : Nat :=
  Nat.land (Nat.shiftRight (popc24 (wordT a)) (nat_lit 2)) (nat_lit 1)

@[expose] noncomputable def pe (P i : Nat) : Nat := fld(P, Nat.mul (nat_lit 5) i, nat_lit 31)

@[expose] noncomputable def permWordT (P w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (selB (bitN w i) (Nat.shiftLeft (nat_lit 1) (pe P i)))) (nat_lit 24)

@[expose] noncomputable def permCT (P a : Nat) : Nat := coeffT (permWordT P (wordT a))

@[expose] noncomputable def permDT (P d : Nat) : Nat := dualT (permWordT P (repT d))

@[expose] noncomputable def betaPT (P i j : Nat) : Nat :=
  Nat.xor (pairT (permCT P (Nat.shiftLeft (nat_lit 1) j)) (thetaT (permCT P (Nat.shiftLeft (nat_lit 1) i))))
    (betaT i j)

@[expose] noncomputable def betaTabT (P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc2 => Nat.lor acc2 (Nat.shiftLeft (betaPT P i j) (Nat.add (Nat.mul (nat_lit 12) i) j)))
      (nat_lit 12))) (nat_lit 12)

@[expose] noncomputable def kappaT (BT a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc2 => Nat.xor acc2 (Nat.land (Nat.land (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
          (Nat.blt i j)) (Nat.land (bitN a i) (bitN a j))) (bitN BT (Nat.add (Nat.mul (nat_lit 12) i) j))))
      (nat_lit 12))) (nat_lit 12)

@[expose] noncomputable def basisImg (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (f (Nat.shiftLeft (nat_lit 1) i)) (Nat.mul (nat_lit 12) i)))
    (nat_lit 12)

@[expose] noncomputable def onesP (S n : Nat) : Nat := ones (Nat.mul S n)

@[expose] noncomputable def repP (S n m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun b acc => Nat.lor acc (Nat.shiftLeft m (Nat.mul b S))) n

@[expose] noncomputable def plin (S MI X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun i acc2 => Nat.xor acc2 (selB (bitN MI (Nat.add (Nat.mul (nat_lit 12) i) k)) (plane S i X)))
        (nat_lit 12)) (Nat.mul k S))) (nat_lit 12)

@[expose] noncomputable def constP (S c m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (selB (bitN c k) m) (Nat.mul k S))) (nat_lit 12)

@[expose] noncomputable def thetaPl (S X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun n acc => Nat.xor acc (Nat.land (repP S (nat_lit 12) (plane S n X))
      (Nat.xor (constP S (packBetaT n) (ones S))
        (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
          (fun m acc2 => Nat.xor acc2 (selB (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.blt m n))
            (constP S (dualT (Nat.land (bmT m) (bmT n))) (plane S m X)))) (nat_lit 12))))) (nat_lit 12)

@[expose] noncomputable def quadPl (S BT X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (Nat.land (plane S i X)
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun j acc2 => Nat.xor acc2 (selB (Nat.land (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
            (Nat.blt i j)) (bitN BT (Nat.add (Nat.mul (nat_lit 12) i) j))) (plane S j X))) (nat_lit 12))))
    (nat_lit 12)

@[expose] noncomputable def parSel (S m X : Nat) : Nat := xorSel S X m

end CFSG.KC.KDense

end
