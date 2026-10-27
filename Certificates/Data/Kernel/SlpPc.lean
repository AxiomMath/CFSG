module

public import CFSG.Certificates.Kernel.Orders.Mat

public section

namespace CFSG.KC.SlpPc

open CFSG.KC.Ord

@[expose] noncomputable def sB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def nthD {α : Type} (d : α) (l : List α) : Nat → α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => α) x (fun j _ => ih j) i) l

@[expose] noncomputable def tl (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun _ xs _ => xs) l

@[expose] noncomputable def lk (ONE : Nat) (bl : List (List Nat)) (cur : List Nat) (n r : Nat) :
    Nat :=
  Bool.rec (motive := fun _ => Nat)
    (nthD ONE (nthD List.nil bl (Nat.sub (Nat.sub (Nat.shiftRight n 6) (Nat.shiftRight r 6)) 1))
      (Nat.sub 63 (Nat.land r 63)))
    (nthD ONE cur (Nat.sub (Nat.sub n 1) r))
    (Nat.beq (Nat.shiftRight r 6) (Nat.shiftRight n 6))

@[expose] noncomputable def runP (mul : Nat → Nat → Nat) (ONE : Nat) (prg : List (Nat × Nat)) :
    List (List Nat) → List Nat → Nat → (List (List Nat) → List Nat → Nat → Bool) → Bool :=
  List.rec
    (motive := fun _ => List (List Nat) → List Nat → Nat → (List (List Nat) → List Nat → Nat → Bool) →
      Bool)
    (fun bl cur n k => k bl cur n)
    (fun p _ ih bl cur n k =>
      sB (mul (lk ONE bl cur n p.1) (lk ONE bl cur n p.2)) fun x =>
      sB (Nat.succ n) fun n1 =>
        Bool.rec (motive := fun _ => Bool) (ih bl (List.cons x cur) n1 k)
          (ih (List.cons (List.cons x cur) bl) List.nil n1 k) (Nat.beq (Nat.land n1 63) 0)) prg

@[expose] noncomputable def wordGo (mul : Nat → Nat → Nat) (R : Nat → Nat) (w : List Nat) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => CFSG.KC.Loop.strictN (mul acc (R l)) ih) w

@[expose] noncomputable def wordP (mul : Nat → Nat → Nat) (ONE : Nat) (R : Nat → Nat)
    (w : List Nat) : Nat :=
  wordGo mul R w ONE

@[expose] noncomputable def mapS {α : Type} (f : α → Nat) (l : List α) :
    (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k List.nil)
    (fun a _ ih k => sB (f a) fun x => ih fun xs => k (List.cons x xs)) l

@[expose] noncomputable def pows (mul : Nat → Nat → Nat) (ONE : Nat) (hs : List Nat) :
    (List (List Nat) → Bool) → Bool :=
  List.rec (motive := fun _ => (List (List Nat) → Bool) → Bool) (fun k => k List.nil)
    (fun h _ ih k => sB (mul h h) fun h2 => sB (mul h2 h) fun h3 => sB (mul h3 h) fun h4 =>
      sB (mul h4 h) fun h5 =>
        ih fun ps => k (List.cons [ONE, h, h2, h3, h4, h5] ps)) hs

@[expose] noncomputable def nfGo (mul : Nat → Nat → Nat) (pw : List (List Nat)) :
    List Nat → Nat → Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ acc => acc)
    (fun row _ ih a acc => (fun e => CFSG.KC.Loop.strictN
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) (mul acc (nthD 0 row e)) (nthD 0 row e)
            (Nat.beq acc 0))
          acc (Nat.beq e 0)) (ih (tl a)))
      (nthD 0 a 0)) pw

@[expose] noncomputable def nfM (mul : Nat → Nat → Nat) (ONE : Nat) (pw : List (List Nat))
    (a : List Nat) : Nat :=
  (fun x => Bool.rec (motive := fun _ => Nat) x ONE (Nat.beq x 0)) (nfGo mul pw a 0)

@[expose] noncomputable def ltUpTo (a : List Nat) (b n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB (Nat.blt (nthD 0 a t) b) ih) n

@[expose] noncomputable def zeroUpTo (a : List Nat) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB (Nat.beq (nthD 0 a t) 0) ih) n

@[expose] noncomputable def relOK (mul : Nat → Nat → Nat) (ONE : Nat) (hs : List Nat)
    (pw : List (List Nat)) (i j : Nat) (e : List Nat) : Bool :=
  andB (ltUpTo e 5 6) (andB (zeroUpTo e (Nat.succ i))
    (Bool.rec (motive := fun _ => Bool)
      (Nat.beq (mul (nthD 0 hs j) (nthD 0 hs i)) (mul (nthD 0 hs i) (nfM mul ONE pw e)))
      (Nat.beq (nthD 0 (nthD List.nil pw i) 5) (nfM mul ONE pw e))
      (Nat.beq i j)))

@[expose] noncomputable def relsOK (mul : Nat → Nat → Nat) (ONE : Nat) (hs : List Nat)
    (pw : List (List Nat)) (rel : List (List Nat)) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun i _ => Nat.beq i 6)
    (fun r _ ih i j => andB (Nat.beq (nthD 0 r 0) i) (andB (Nat.beq (nthD 0 r 1) j)
      (andB (relOK mul ONE hs pw i j (tl (tl r)))
        (Bool.rec (motive := fun _ => Bool) (ih i (Nat.succ j)) (ih (Nat.succ i) (Nat.succ i))
          (Nat.beq j 5))))) rel

@[expose] noncomputable def rowK (S k M : Nat) : Nat := rowsOf S k 1 M

@[expose] noncomputable def bwOK (L : Nat) (bw : Nat) : Bool :=
  (fun Lb => andB (validM 5 (Nat.mul 9 1729) Lb (Nat.shiftLeft Lb 12) bw)
    (Nat.rec (motive := fun _ => Bool) true
      (fun k ih => andB (Nat.beq (Nat.land (rowK 1729 k bw) (Nat.sub (Nat.shiftLeft 1 117) 1))
        (Nat.shiftLeft 1 (Nat.mul 13 k))) ih) 9))
    (Nat.land L (Nat.sub (Nat.shiftLeft 1 (Nat.mul 9 1729)) 1))

@[expose] noncomputable def invOne (vec : Nat → Nat → Nat) (LV HV RM bw h h' : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => andB (Nat.beq (vec (rowK 1729 k bw) h)
      (redP 13 LV HV 5 9 (vecU 13 1729 9 RM (rowK 117 k h') bw))) ih) 9

@[expose] noncomputable def invOK (vec : Nat → Nat → Nat) (LV HV RM bw : Nat) (hs hwm : List Nat) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB (invOne vec LV HV RM bw (nthD 0 hs i) (nthD 0 hwm i)) ih) 6

@[expose] noncomputable def hwmOK (L9 H9 : Nat) (hwm : List Nat) : Bool :=
  andB (Nat.beq hwm.length 6)
    (List.rec (motive := fun _ => Bool) true
      (fun M _ ih => andB (validM 5 (Nat.mul 81 13) L9 H9 M) ih) hwm)

@[expose] noncomputable def fusOK (mul : Nat → Nat → Nat) (ONE : Nat) (R : Nat → Nat)
    (pw : List (List Nat)) (wr : List Nat) (fus : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun f _ ih => andB (andB (ltUpTo f 5 6) (andB (Nat.blt (nthD 0 f 7) 5)
      ((fun C => Nat.beq (mul (nfM mul ONE pw f) C) (mul C (R (nthD 0 wr (nthD 0 f 7)))))
        (R (nthD 0 f 6))))) ih) fus

@[expose] noncomputable def chkJ (mul vec : Nat → Nat → Nat) (A B ONE L LV HV RM L9 H9 : Nat)
    (prg : List (Nat × Nat)) (wg wr : List Nat) (hw rel fus : List (List Nat)) (bw : Nat)
    (hwm : List Nat) : Bool :=
  runP mul ONE prg List.nil [B, A, ONE] 3 fun bl cur n =>
    mapS (fun w => wordP mul ONE (fun l => lk ONE bl cur n (nthD 0 wg l)) w) hw fun hs =>
    pows mul ONE hs fun pw =>
      andB (Nat.beq hs.length 6) (andB (relsOK mul ONE hs pw rel 0 0)
        (andB (hwmOK L9 H9 hwm) (andB (bwOK L bw) (andB (invOK vec LV HV RM bw hs hwm)
          (fusOK mul ONE (lk ONE bl cur n) pw wr fus)))))

@[expose] noncomputable def key (keyc : List Nat) (u : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun c _ ih acc => ih (Nat.add (Nat.mul acc 5) (bitsN u (Nat.mul 13 c) 13))) keyc 0

@[expose] noncomputable def code (a : List Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun t ih => Nat.add (Nat.mul ih 5) (nthD 0 a t)) 6

@[expose] noncomputable def maskOf (l : List (List Nat)) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun a _ ih acc => CFSG.KC.Loop.strictN (Nat.lor acc (Nat.shiftLeft 1 (code a))) ih) l acc

@[expose] noncomputable def actW (vec : Nat → Nat → Nat) (Ms : List Nat) (a : List Nat) :
    Nat → Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ u => u)
    (fun M _ ih a u => ih (tl a)
      (Nat.rec (motive := fun _ => Nat) u (fun _ acc => CFSG.KC.Loop.strictN (vec acc M) id)
        (nthD 0 a 0))) Ms a

@[expose] noncomputable def othOK (vec : Nat → Nat → Nat) (Ms : List Nat) (c0 : Nat)
    (oth : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a _ ih => andB (andB (ltUpTo a 5 6) (notB (Nat.beq (Nat.rec (motive := fun _ => Nat) c0
      (fun _ u => CFSG.KC.Loop.strictN (actW vec Ms a u) id) 5) c0))) ih) oth

@[expose] noncomputable def leaf (vec : Nat → Nat → Nat) (Ms : List Nat) (keyc : List Nat)
    (dep jb msk s0 s1 s2 m mask : Nat) (k : Nat → Nat → Bool) : Bool :=
  sB (key keyc s0) fun k0 =>
  andB (Nat.beq (bitsN mask k0 1) 0) (sB (bitsN dep (Nat.mul 4 k0) 4) fun d0 =>
  andB (Bool.rec (motive := fun _ => Bool)
      ((fun j => Nat.beq (Nat.succ (bitsN dep (Nat.mul 4
          (key keyc (vec (Bool.rec (motive := fun _ => Nat) s2 s1 (Nat.beq j 0)) (nthD 0 Ms j))))
          4)) d0) (bitsN jb m 1))
      (orB (Nat.beq m 0) (Nat.beq (bitsN msk m 1) 1))
      (Nat.beq d0 0))
    (sB (Nat.lor mask (Nat.shiftLeft 1 k0)) fun mask' => sB (Nat.succ m) fun m' => k m' mask'))

@[expose] noncomputable def loop5 (vec : Nat → Nat → Nat) (M : Nat)
    (ih : Nat → Nat → Nat → Nat → Nat → (Nat → Nat → Bool) → Bool) :
    Nat → Nat → Nat → Nat → Nat → (Nat → Nat → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → (Nat → Nat → Bool) → Bool)
    (fun _ _ _ m mask k => k m mask)
    (fun n jh s0 s1 s2 m mask k => ih s0 s1 s2 m mask fun m' mask' =>
      Bool.rec (motive := fun _ => Bool)
        (sB (vec s0 M) fun t0 => sB (vec s1 M) fun t1 => sB (vec s2 M) fun t2 =>
          jh t0 t1 t2 m' mask' k)
        (k m' mask') (Nat.beq n 0)) 5

@[expose] noncomputable def nest (vec : Nat → Nat → Nat) (Ms : List Nat) (keyc : List Nat)
    (dep jb msk : Nat) (Ns : List Nat) :
    Nat → Nat → Nat → Nat → Nat → (Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → (Nat → Nat → Bool) → Bool)
    (fun s0 s1 s2 m mask k => leaf vec Ms keyc dep jb msk s0 s1 s2 m mask k)
    (fun M _ ih => loop5 vec M ih) Ns

@[expose] noncomputable def pow4 (vec : Nat → Nat → Nat) (M u : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) u (fun _ acc => CFSG.KC.Loop.strictN (vec acc M) id) 4

@[expose] noncomputable def chkW (vec : Nat → Nat → Nat) (L9 H9 CM9 RM9 ONE9 LV9 HV9 : Nat)
    (hwm : List Nat) (c0 : Nat) (keyc : List Nat) (dep jb : Nat) (fus oth : List (List Nat)) :
    Bool :=
  andB (constsOK 5 13 117 9 9 L9 H9 CM9 RM9 ONE9 LV9 HV9) (andB (hwmOK L9 H9 hwm)
  (andB (validM 5 117 LV9 HV9 c0) (andB (List.rec (motive := fun _ => Bool) true
      (fun f _ ih => andB (ltUpTo f 5 6) ih) fus) (andB (othOK vec hwm c0 oth)
  (sB (maskOf oth (maskOf fus 0)) fun msk =>
    sB (pow4 vec (nthD 0 hwm 0) c0) fun c1 => sB (pow4 vec (nthD 0 hwm 1) c0) fun c2 =>
      nest vec hwm keyc dep jb msk hwm c0 c1 c2 0 0 fun m _ => Nat.beq m 15625)))))

end CFSG.KC.SlpPc

end
