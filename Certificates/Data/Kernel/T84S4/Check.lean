module

public import Certificates.Data.Kernel.Misc.T84K

public section

namespace CFSG.KD.T84S4

open CFSG.KC.Misc CFSG.KC.Misc.T84

@[expose] noncomputable def l4 (X p : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul 4 p)) 15

@[expose] noncomputable def l8 (X p : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul 8 p)) 255

@[expose] noncomputable def l16 (X p : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul 16 p)) 65535

@[expose] noncomputable def mI (ACT TM i j : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.xor (Nat.div i 12)
      (l4 ACT (Nat.add (Nat.mul 16 (Nat.mod i 12)) (Nat.div j 12)))) 12)
    (l4 TM (Nat.add (Nat.mul 12 (Nat.mod i 12)) (Nat.mod j 12)))

@[expose] noncomputable def eC (TC i : Nat) : Nat := mkT (Nat.div i 12) (l16 TC (Nat.mod i 12))

@[expose] noncomputable def sel (d a b c : Nat) : Nat :=
  Bool.rec (Bool.rec (Bool.rec 0 a (Nat.beq d 1)) b (Nat.beq d 2)) c (Nat.beq d 3)

@[expose] noncomputable def ev2 (ACT TM a b c w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun acc _ => acc)
    (fun _ ih acc w => ih (mI ACT TM acc (sel (Nat.land w 3) a b c)) (Nat.shiftRight w 2)) 9 0 w

@[expose] noncomputable def phi2 (ACT TM WP a b c x : Nat) : Nat := ev2 ACT TM a b c (l16 WP x)

@[expose] noncomputable def inL (x : Nat) (l : List Nat) : Bool :=
  List.rec false (fun y _ ih => Bool.or (Nat.beq x y) ih) l

@[expose] noncomputable def setB (p : Nat → Bool) (l : List Nat) (n : Nat) : Bool :=
  Nat.rec true (fun x ih => Bool.and ih (Bool.rec (Bool.not (inL x l)) (inL x l) (p x))) n

@[expose] noncomputable def listB (ACT TM : Nat) (L3 L4 I2 : List Nat) : Bool :=
  Bool.and (setB (fun x => Nat.beq (mI ACT TM (mI ACT TM x x) x) 0) L3 192)
    (Bool.and (setB (fun x => Nat.beq (mI ACT TM (mI ACT TM x x) (mI ACT TM x x)) 0) L4 192)
      (Bool.and (setB (fun x => Nat.beq (mI ACT TM x x) 0) I2 192)
        (List.rec true (fun y _ ih => Bool.and (Nat.blt y 192) ih) (L3 ++ L4 ++ I2))))

@[expose] noncomputable def wordsB (ACT TM WP : Nat) : Bool :=
  Nat.rec true (fun x ih => Bool.and ih (Nat.beq (phi2 ACT TM WP 191 169 156 x) x)) 192

@[expose] noncomputable def fixJ2 (ACT TM WP a b c : Nat) : Nat × Bool :=
  Nat.rec (motive := fun _ => Nat × Bool) (0, true)
    (fun t ih => (fun x => Bool.rec ih (Nat.succ ih.1, Bool.and ih.2 (Nat.beq (mI ACT TM x x) 0))
      (Nat.beq (phi2 ACT TM WP a b c x) x)) (Nat.add (Nat.mul 12 (Nat.div t 4)) (Nat.mod t 4))) 64

@[expose] noncomputable def anyY2 (ACT TM WP a b c : Nat) (L3 : List Nat) : Bool :=
  List.rec false
    (fun y _ ih => Bool.or (Bool.and (Nat.blt 0 y) (Nat.beq (phi2 ACT TM WP a b c y) y)) ih) L3

@[expose] noncomputable def finK2 (ACT TM WP : Nat) (L3 : List Nat) (a b c : Nat) : Bool :=
  Bool.rec true
    (Bool.rec true
      ((fun F : Nat × Bool => Bool.rec true (Bool.rec true (anyY2 ACT TM WP a b c L3) F.2)
          (Nat.beq F.1 4)) (fixJ2 ACT TM WP a b c))
      (Bool.and (Nat.beq (phi2 ACT TM WP a b c b) 169) (Nat.beq (phi2 ACT TM WP a b c c) 156)))
    (Nat.beq (phi2 ACT TM WP a b c a) 191)

@[expose] noncomputable def sOf (ACT TM a : Nat) (I2 : List Nat) : List Nat :=
  List.rec [] (fun c _ ih => Bool.rec ih (c :: ih) (Nat.beq (ev2 ACT TM a 0 c 3549) 0)) I2

@[expose] noncomputable def loopC2 (ACT TM WP : Nat) (L3 : List Nat) (a b A : Nat) (S : List Nat) :
    Bool :=
  List.rec true (fun c _ ih =>
    Bool.and (Bool.rec true (finK2 ACT TM WP L3 a b c)
      (Nat.beq (mI ACT TM (mI ACT TM (mI ACT TM A c) b) c) 0)) ih) S

@[expose] noncomputable def loopB2 (ACT TM WP : Nat) (L3 L4 : List Nat) (a : Nat) (S : List Nat) :
    Bool :=
  List.rec true (fun b _ ih =>
    Bool.and (Bool.rec true (loopC2 ACT TM WP L3 a b (ev2 ACT TM a b 0 1446) S)
      (Bool.and (Nat.beq (ev2 ACT TM a b 0 170) 0) (Nat.beq (ev2 ACT TM a b 0 1638) 0))) ih) L4

@[expose] noncomputable def enumB (ACT TM WP : Nat) (L3 L4 I2 hs : List Nat) : Bool :=
  List.rec true (fun a _ ih => Bool.and (loopB2 ACT TM WP L3 L4 a (sOf ACT TM a I2)) ih) hs

@[expose] noncomputable def jB (j : Nat) : Bool := Nat.blt (Nat.mod j 12) 4

@[expose] noncomputable def invB (ACT TM INV : Nat) : Bool :=
  Nat.rec true (fun i ih => Bool.and ih
    (Bool.and (Nat.blt (l8 INV i) 192) (Nat.beq (mI ACT TM i (l8 INV i)) 0))) 192

@[expose] noncomputable def normB (ACT TM INV : Nat) : Bool :=
  Nat.rec true (fun i ih => Bool.and ih (Nat.rec true (fun j ih' => Bool.and ih'
    (Bool.rec true (jB (mI ACT TM (mI ACT TM i j) (l8 INV i))) (jB j))) 192)) 192

@[expose] noncomputable def gen3B (ACT TM : Nat) : Bool :=
  Bool.and (Nat.beq (mI ACT TM (mI ACT TM 191 191) 191) 0)
    (Nat.rec true (fun i ih => Bool.and ih
      (Bool.or (Nat.beq (mI ACT TM (mI ACT TM i i) i) 0)
        ((fun y => Nat.beq (mI ACT TM (mI ACT TM y y) y) 0) (mI ACT TM i 191)))) 192)

@[expose] noncomputable def fpfB (ACT TM : Nat) : Bool :=
  Nat.rec true (fun i ih => Bool.and ih
    (Bool.rec true
      (Nat.rec true (fun j ih' => Bool.and ih'
        (Bool.rec true (Bool.or (Nat.beq j 0)
          (Bool.not (Nat.beq (mI ACT TM i j) (mI ACT TM j i)))) (jB j))) 192)
      (Bool.and (Nat.blt 0 i) (Nat.beq (mI ACT TM (mI ACT TM i i) i) 0)))) 192

@[expose] noncomputable def tabB (ACT TM TC lo n : Nat) : Bool :=
  Nat.rec true (fun t ih => Bool.and ih ((fun i => Nat.rec true (fun j ih' => Bool.and ih'
    (Nat.beq (mulT (eC TC i) (eC TC j)) (eC TC (mI ACT TM i j)))) 192) (Nat.add lo t))) n

@[expose] noncomputable def pow44T (z : Nat) : Nat :=
  (fun z2 => (fun z4 => (fun z8 => (fun z32 => mulT z32 (mulT z8 z4))
    (mulT (mulT z8 z8) (mulT z8 z8))) (mulT z4 z4)) (mulT z2 z2)) (mulT z z)

@[expose] noncomputable def inTC (TC z : Nat) : Bool :=
  Nat.rec false (fun k ih => Bool.or ih (Nat.beq (hiT z) (l16 TC k))) 12

@[expose] noncomputable def oddOne (TC z : Nat) : Bool :=
  (fun p => Bool.rec true
    (Bool.rec true (inTC TC z)
      (Bool.and (memJ (mulT (mulT z (eC TC 50)) p)) (Bool.and (memJ (mulT (mulT z (eC TC 181)) p))
        (Bool.and (memJ (mulT (mulT z (eC TC 158)) p)) (memJ (mulT (mulT z (eC TC 110)) p))))))
    (Nat.beq (mulT z p) oneT)) (pow44T z)

@[expose] noncomputable def relsB (ACT TM : Nat) : Bool :=
  Bool.and (Nat.beq (mI ACT TM (mI ACT TM 191 191) 191) 0)
    (Bool.and (Nat.beq (mI ACT TM (mI ACT TM 169 169) (mI ACT TM 169 169)) 0)
      (Bool.and (Nat.beq (mI ACT TM 156 156) 0)
        (Bool.and (Nat.beq (ev2 ACT TM 191 169 156 170) 0)
          (Bool.and (Nat.beq (ev2 ACT TM 191 169 156 1638) 0)
            (Bool.and (Nat.beq (ev2 ACT TM 191 169 156 3549) 0)
              (Nat.beq (ev2 ACT TM 191 169 156 243110) 0))))))

@[expose] noncomputable def boundB (ACT TM : Nat) : Bool :=
  Nat.rec true (fun i ih => Bool.and ih
    (Nat.rec true (fun j ih' => Bool.and ih' (Nat.blt (mI ACT TM i j) 192)) 192)) 192

@[expose] noncomputable def injB (TC : Nat) : Bool :=
  Nat.rec true (fun i ih => Bool.and ih
    (Nat.rec true (fun j ih' => Bool.and ih'
      (Bool.or (Nat.beq i j) (Bool.not (Nat.beq (eC TC i) (eC TC j))))) 192)) 192

@[expose] noncomputable def jEqB (TC : Nat) : Bool :=
  Nat.rec true (fun i ih => Bool.and ih
    (Bool.rec (Bool.not (memJ (eC TC i))) (memJ (eC TC i)) (jB i))) 192

@[expose] noncomputable def tcB (TC : Nat) : Bool :=
  Nat.rec true (fun k ih => Bool.and ih (memN (l16 TC k) S0L)) 12

@[expose] noncomputable def jkB (TC : Nat) : Bool :=
  List.rec true (fun y _ ih => Bool.and
    (Nat.rec false (fun i ih' => Bool.or ih' (Nat.beq (eC TC i) y)) 192) ih) JK

@[expose] noncomputable def oddB (TC lo n : Nat) : Bool :=
  Nat.rec true (fun t ih => Bool.and ih
    (List.rec true (fun m _ ih' => Bool.and ih' (oddOne TC (mkT (Nat.add lo t) m))) S0L)) n

end CFSG.KD.T84S4

end
