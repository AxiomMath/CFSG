module

public import Certificates.Data.Kernel.O8.Core
public import CFSG.Certificates.Kernel.Local.Core

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M

@[expose] noncomputable def colAt (C d : Nat) : Nat := fget C d (nat_lit 6)

@[expose] noncomputable def colsActK (C z : Nat) : Nat :=
  xorN (nat_lit 6) fun d => nIf(Nat.beq (bitN z d) (nat_lit 1), colAt C d, nat_lit 0)

@[expose] noncomputable def bfTab (e : Nat) : Nat :=
  orN (nat_lit 64) fun x => Nat.shiftLeft
    (orN (nat_lit 64) fun c => Nat.shiftLeft (bfK e x c) c) (Nat.mul (nat_lit 64) x)

@[expose] noncomputable def qMask (e : Nat) : Nat := orN (nat_lit 64) fun c => Nat.shiftLeft (qK e c) c

@[expose] noncomputable def candK (e : Nat) (BT QM C k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    (nIf(Nat.beq (qK e (pw2 k)) (nat_lit 1), QM, Nat.xor QM (maskN (nat_lit 64))))
    (fun i ih => strictN ih fun m => Nat.land m
      (nIf(Nat.beq (bfK e (pw2 i) (pw2 k)) (nat_lit 1), fget BT (colAt C i) (nat_lit 64),
        Nat.xor (fget BT (colAt C i) (nat_lit 64)) (maskN (nat_lit 64)))))
    k

@[expose] noncomputable def walkK (e : Nat) (BT QM : Nat) (f : Nat → Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) f
    (fun d ih C => (fun k => CFSG.KC.Local.wordFold (fun c s => Nat.add s (ih (Nat.lor C (Nat.shiftLeft c (Nat.mul (nat_lit 6) k)))))
        (nat_lit 0) (candK e BT QM C k) (nat_lit 0))
      (Nat.sub (nat_lit 5) d))

@[expose] noncomputable def walkFrom (e : Nat) (f : Nat → Nat) (c : Nat) : Nat :=
  strictN (bfTab e) fun BT => strictN (qMask e) fun QM =>
    nIf(Nat.beq (bitN (candK e BT QM (nat_lit 0) (nat_lit 0)) c) (nat_lit 1),
      walkK e BT QM f (nat_lit 5) c, nat_lit 0)

@[expose] noncomputable def lead6 (r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b ih => nIf(Nat.beq (bitN r b) (nat_lit 1), b, ih)) (nat_lit 6)

@[expose] noncomputable def dickK (C : Nat) : Nat :=
  Nat.land (Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun j ih P => (fun v => (fun r => nIf(Nat.beq r (nat_lit 0), ih P,
          Nat.add (nat_lit 1) (ih (Nat.lor P (Nat.shiftLeft r (Nat.mul (nat_lit 6) (lead6 r)))))))
        (Nat.rec (motive := fun _ => Nat) v (fun b ih2 => strictN ih2 fun u =>
            (fun t => nIf(Nat.beq (bitN u t) (nat_lit 1), Nat.xor u (fget P t (nat_lit 6)), u))
              (Nat.sub (nat_lit 5) b)) (nat_lit 6)))
      (Nat.xor (colAt C j) (pw2 j)))
    (nat_lit 6) (nat_lit 0)) (nat_lit 1)

@[expose] noncomputable def involK (C : Nat) : Bool :=
  andB (allN (nat_lit 6) fun j => Nat.beq (colsActK C (colAt C j)) (pw2 j))
    (notB (Nat.beq C (nat_lit 34630287489)))

@[expose] noncomputable def fixK (C : Nat) : Nat :=
  sumN (nat_lit 64) fun z => nIf(Nat.beq (colsActK C z) z, nat_lit 1, nat_lit 0)

@[expose] noncomputable def invBadK (C : Nat) : Nat :=
  nIf(Nat.beq (dickK C) (nat_lit 1), nat_lit 0,
    nIf(involK C, nIf(Nat.beq (fixK C) (nat_lit 16), nat_lit 0, nat_lit 1), nat_lit 0))

@[expose] noncomputable def formOK (e : Nat) : Bool :=
  andB (Nat.beq (qK e (nat_lit 0)) (nat_lit 0))
    (andB (allN (nat_lit 64) fun x => allN (nat_lit 64) fun y => allN (nat_lit 64) fun z =>
        Nat.beq (bfK e (Nat.xor x y) z) (Nat.xor (bfK e x z) (bfK e y z)))
      (allN (nat_lit 63) fun x => notB (allN (nat_lit 64) fun y =>
        Nat.beq (bfK e (Nat.succ x) y) (nat_lit 0))))

@[expose] noncomputable def colsOfRows (M : Nat) : Nat :=
  orN (nat_lit 6) fun j => Nat.shiftLeft (bvecK M (pw2 j)) (Nat.mul (nat_lit 6) j)

@[expose] noncomputable def genOK (e : Nat) (G GI : Nat) : Bool :=
  allN (nat_lit 6) fun i => andB (Nat.beq (bmulK (mat G i) (mat GI i)) ID6)
    (andB (Nat.beq (bmulK (mat GI i) (mat G i)) ID6)
      (allN (nat_lit 64) fun x => Nat.beq (qK e (bvecK (mat G i) x)) (qK e x)))

@[expose] noncomputable def genDickOK (G GI : Nat) : Bool :=
  allN (nat_lit 6) fun i => andB (Nat.beq (dickK (colsOfRows (mat G i))) (nat_lit 0))
    (Nat.beq (dickK (colsOfRows (mat GI i))) (nat_lit 0))

@[expose] noncomputable def wordActK (G : Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun i _ ih => bvecK (mat G i) ih) w

@[expose] noncomputable def wordAt (OW : List (List Nat)) (x : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih i => Nat.rec (motive := fun _ => List Nat) w (fun i' _ => ih i') i) OW x

@[expose] noncomputable def orbitOK (e : Nat) (G n0 : Nat) (OW : List (List Nat)) : Bool :=
  allN (nat_lit 64) fun x => orB (Nat.beq x (nat_lit 0))
    (Nat.beq (wordActK G (wordAt OW x) (nIf(Nat.beq (qK e x) (nat_lit 1), n0, nat_lit 1))) x)

@[expose] noncomputable def affK (D x : Nat) : Nat :=
  Nat.xor (bvecK (Nat.land D (maskN (nat_lit 36))) x) (Nat.shiftRight D (nat_lit 36))

@[expose] noncomputable def coneOK (e : Nat) (X Xi Y Yi CC : Nat) : Bool :=
  andB (allN (nat_lit 64) fun v =>
      andB (Nat.beq (qK e (affK X v)) (qK e v)) (andB (Nat.beq (qK e (affK Y v)) (qK e v))
        (andB (Nat.beq (affK Xi (affK X v)) v) (andB (Nat.beq (affK X (affK Xi v)) v)
          (andB (Nat.beq (affK Yi (affK Y v)) v) (Nat.beq (affK Y (affK Yi v)) v))))))
    (andB (allN (nat_lit 6) fun j =>
        Nat.beq (affK X (affK Y (affK Xi (affK Yi (pw2 j))))) (colAt CC j))
      (andB (Nat.beq (affK X (affK Y (affK Xi (affK Yi (nat_lit 0))))) (nat_lit 0))
        (Nat.beq (dickK CC) (nat_lit 1))))

end CFSG.KC.O8

end
