module

public import Certificates.Data.Kernel.Sp4Ov.Lines

public section

namespace CFSG.KD.Sp4Ov

open CFSG.KC.Loop

@[expose] noncomputable def f4mK (x y : Nat) : Nat :=
  Nat.lor (Nat.xor (Nat.land (Nat.land x y) 1)
      (Nat.land (Nat.land (Nat.shiftRight x 1) (Nat.shiftRight y 1)) 1))
    (Nat.shiftLeft (Nat.xor (Nat.xor (Nat.land (Nat.land x (Nat.shiftRight y 1)) 1)
      (Nat.land (Nat.land (Nat.shiftRight x 1) y) 1))
      (Nat.land (Nat.land (Nat.shiftRight x 1) (Nat.shiftRight y 1)) 1)) 1)

@[expose] noncomputable def psiK (v : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.mul fld(v, 0, 1) 1) (Nat.mul fld(v, 1, 1) 4))
    (Nat.xor (Nat.mul fld(v, 2, 1) 6) (Nat.mul fld(v, 3, 1) 13))

@[expose] noncomputable def smulK (c w : Nat) : Nat :=
  Nat.lor (f4mK c fld(w, 0, 3)) (Nat.shiftLeft (f4mK c fld(w, 2, 3)) 2)

@[expose] noncomputable def matK (c1 c2 w : Nat) : Nat :=
  Nat.xor (smulK fld(w, 0, 3) c1) (smulK fld(w, 2, 3) c2)

@[expose] noncomputable def frobK (w : Nat) : Nat :=
  Nat.lor (f4mK fld(w, 0, 3) fld(w, 0, 3)) (Nat.shiftLeft (f4mK fld(w, 2, 3) fld(w, 2, 3)) 2)

@[expose] noncomputable def psiInvK (T w : Nat) : Nat := fld(T, Nat.shiftLeft w 2, 15)

@[expose] noncomputable def allV (f : Nat → Bool) : Bool := all16 f

@[expose] noncomputable def semK (T d : Nat) : Nat :=
  (fun c1 c2 => Nat.lor (Nat.lor c1 (Nat.shiftLeft c2 4))
    (nIf(allV fun v => Nat.beq (psiK (mv d v)) (matK c1 c2 (psiK v)), 0, 256)))
  (psiK (mv d (psiInvK T 1))) (psiK (mv d (psiInvK T 4)))

@[expose] noncomputable def semOkK (T d : Nat) : Bool :=
  (fun c => (fun c1 c2 k => bAnd(allV fun v => Nat.beq (psiK (mv d v))
      (matK c1 c2 (nIf(Nat.beq k 0, psiK v, frobK (psiK v)))),
    Nat.beq (Nat.xor (f4mK fld(c1, 0, 3) fld(c2, 2, 3)) (f4mK fld(c2, 0, 3) fld(c1, 2, 3))) 1))
    fld(c, 0, 15) fld(c, 4, 15) fld(c, 8, 1)) (semK T d)

@[expose] noncomputable def ptK (P w : Nat) : Nat := fld(P, Nat.mul 3 w, 7)

@[expose] noncomputable def ptCode (i : Nat) : Nat := fld(nat_lit 890177, Nat.shiftLeft i 2, 15)

@[expose] noncomputable def permK (T P d : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.lor ih
    (Nat.shiftLeft (ptK P (psiK (mv d (psiInvK T (ptCode i))))) (Nat.mul 3 i))) 5

@[expose] noncomputable def appP (p i : Nat) : Nat := fld(p, Nat.mul 3 i, 7)

@[expose] noncomputable def lineMapK (T P d p : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(
    (fun w => Nat.beq (ptK P (psiK (mv d (psiInvK T w)))) (appP p (ptK P w))) (Nat.succ j), ih)) 15

@[expose] noncomputable def compK (p q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.lor ih
    (Nat.shiftLeft (appP p (appP q i)) (Nat.mul 3 i))) 5

@[expose] noncomputable def idP : Nat := 18056

@[expose] noncomputable def permOKK (p : Nat) : Bool :=
  bAnd(Nat.beq (Nat.rec (motive := fun _ => Nat) 0
      (fun i ih => Nat.lor ih (Nat.shiftLeft 1 (appP p i))) 5) 31, Nat.blt p 32768)

@[expose] noncomputable def parK (p : Nat) : Nat :=
  Nat.land (Nat.rec (motive := fun _ => Nat) 0 (fun j ih => Nat.add ih
    (Nat.rec (motive := fun _ => Nat) 0 (fun i ih2 => Nat.add ih2
      (nIf(Nat.blt (appP p j) (appP p i), 1, 0))) j)) 5) 1

@[expose] noncomputable def allL (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) l

@[expose] noncomputable def anyL (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => bIf(f x, true, ih)) l

@[expose] noncomputable def all2 (l q : List Nat) (f : Nat → Nat → Bool) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun q => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) q)
    (fun x _ ih q => List.rec (motive := fun _ => Bool) false (fun p q' _ => bAnd(f x p, ih q')) q)
    l q

@[expose] noncomputable def cntL (l : List Nat) (f : Nat → Bool) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add (nIf(f x, 1, 0)) ih) l

@[expose] noncomputable def lenL (l : List Nat) : Nat := cntL l fun _ => true

@[expose] noncomputable def incL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih b => bAnd(Nat.ble b x, bAnd(Nat.blt x 65536, ih (Nat.succ x)))) l 0

@[expose] noncomputable def maskL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun m => m)
    (fun x _ ih m => strictN (Nat.lor m (Nat.shiftLeft 1 x)) ih) l 0

@[expose] noncomputable def closedL (l : List Nat) (m : Nat) : Bool :=
  allL l fun x => allL l fun y => memP m (mulP x y)

@[expose] noncomputable def commAll (l : List Nat) (x : Nat) : Bool := allL l fun y => commK x y

@[expose] noncomputable def powK (x n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) oneP (fun _ ih => mulP ih x) n

@[expose] noncomputable def tabsOK (T P : Nat) : Bool :=
  bAnd(allV fun w => Nat.beq (psiK (psiInvK T w)) w,
    allV fun w => Nat.beq (ptK P w)
      (Nat.rec (motive := fun _ => Nat) 0 (fun i ih =>
        (fun j => nIf(bIf(Nat.beq (smulK 1 (ptCode j)) w, true, bIf(Nat.beq (smulK 2 (ptCode j)) w,
          true, Nat.beq (smulK 3 (ptCode j)) w)), j, ih)) (Nat.sub 4 i)) 5))

@[expose] noncomputable def specialChecksK (spM : Nat) (sp : SpecR) (A B S36 S120 P9 SP : List Nat)
    (p9M : Nat) (permL : List Nat) (T P : Nat) : List Bool :=
  (fun s36 a36 b36 s120 m60 =>
  [Nat.beq (lenL A) 6, Nat.beq (lenL B) 6, Nat.beq (lenL S36) 36,
    incL A, incL B, incL S36, incL S120,
    Nat.beq a36 (maskL A), Nat.beq b36 (maskL B), Nat.beq s36 (maskL S36),
    Nat.beq s120 (maskL S120),
    anyL A (fun x => anyL A fun y => bIf(commK x y, false, true)),
    anyL B (fun x => anyL B fun y => bIf(commK x y, false, true)),
    allL A (fun x => commAll B x),
    allL A (fun x => bIf(memP b36 x, Nat.beq x oneP, true)),
    true, true, true, true,
    closedL A a36, closedL B b36, memP a36 oneP, memP b36 oneP,
    subP a36 s36, subP b36 s36,
    allL S120 (fun x => bIf(memP m60 x,
      allL S120 fun y => bIf(memP m60 y, memP m60 (mulP x y), true), true)),
    true,
    Nat.beq (lenL S120) 120, allL S120 (semOkK T),
    Nat.beq m60 (maskL (List.rec (motive := fun _ => List Nat) []
      (fun x _ ih => Bool.rec (motive := fun _ => List Nat) ih (x :: ih)
        (Nat.beq fld(semK T x, 8, 1) 0)) S120)),
    Nat.beq (cntL S120 (memP m60)) 60,
    allV (fun v => allV fun w => bIf(Nat.beq (psiK v) (psiK w), Nat.beq v w, true)),
    bAnd(all2 S120 permL (fun d p => Nat.beq (permK T P d) p), all2 S120 permL (lineMapK T P)),
    allL S120 (fun d => allV fun v => Nat.beq (psiK (mv d v))
      ((fun c => matK fld(c, 0, 15) fld(c, 4, 15)
        (nIf(Nat.beq fld(c, 8, 1) 0, psiK v, frobK (psiK v)))) (semK T d))),
    allV (fun x => allV fun y => Nat.beq (psiK (Nat.xor x y)) (Nat.xor (psiK x) (psiK y))),
    allV (fun v => allV fun w => bIf(Nat.beq (psiK v) (psiK w), Nat.beq v w, true)),
    allL permL permOKK,
    closedL S120 s120,
    all2 S120 permL (fun d p => bIf(Nat.beq p idP, Nat.beq d oneP, true)),
    all2 S120 permL (fun d p => bIf(Nat.beq fld(semK T d, 8, 1) 0, Nat.beq (parK p) 0, true)),
    allL S120 (fun d => Bool.rec (motive := fun _ => Bool) (Nat.beq fld(semK T d, 8, 1) 1)
      (Nat.beq fld(semK T d, 8, 1) 0) (memP m60 d)),
    Nat.beq (lenL P9) 9, incL P9, true, closedL P9 p9M, memP p9M oneP, Nat.beq p9M (maskL P9),
    subP p9M s36,
    allL S36 (fun g => allL P9 fun x => anyL P9 fun y => Nat.beq (mulP g x) (mulP y g)),
    allL S36 (fun x => bIf(ord3K x, memP p9M x, true)),
    allL P9 (fun x => commAll P9 x),
    allL P9 (fun x => Nat.beq (mulP x (mulP x x)) oneP),
    bAnd(Nat.beq (maskL SP) spM, allL SP fun x => bIf(Nat.beq (powK x 9) oneP,
      Nat.beq (mulP x (mulP x x)) oneP, true)),
    tabsOK T P])
  sp.1 sp.2.1 sp.2.2.1 sp.2.2.2.1 sp.2.2.2.2

@[expose] noncomputable def specialK (spM : Nat) (sp : SpecR) (A B S36 S120 P9 SP : List Nat)
    (p9M : Nat) (permL : List Nat) (T P : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun b _ ih => bAnd(b, ih))
    (specialChecksK spM sp A B S36 S120 P9 SP p9M permL T P)

end CFSG.KD.Sp4Ov

end
