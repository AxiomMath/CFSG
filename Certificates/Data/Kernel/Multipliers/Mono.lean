module

public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Mono

open CFSG.KC CFSG.KC.Loop

@[expose] noncomputable def allR (lo n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB (p (Nat.add lo k)) ih) n

@[expose] noncomputable def ent (T : Nat → Nat) (L x c : Nat) : Nat := T (Nat.add (Nat.mul x L) c)

@[expose] noncomputable def img (e : Nat) : Nat := Nat.land e (nat_lit 65535)

@[expose] noncomputable def lab (e : Nat) : Nat := Nat.shiftRight e (nat_lit 16)

@[expose] noncomputable def step (T : Nat → Nat) (L n st c : Nat) : Nat :=
  strictN (ent T L (Nat.land st (nat_lit 65535)) c) (fun e =>
    Nat.add (img e) (Nat.shiftLeft
      (Nat.mod (Nat.add (Nat.shiftRight st (nat_lit 16)) (lab e)) n) (nat_lit 16)))

@[expose] noncomputable def walk (T : Nat → Nat) (L n : Nat) (w : List Nat) (st : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun c _ ih s => strictN (step T L n s c) ih) w st

@[expose] noncomputable def rangeOK (T : Nat → Nat) (m N n x : Nat) : Bool :=
  allR (nat_lit 0) (Nat.add m m) fun c =>
    andB (Nat.blt (img (ent T (Nat.add m m) x c)) N) (Nat.blt (lab (ent T (Nat.add m m) x c)) n)

@[expose] noncomputable def pairOK (T : Nat → Nat) (L n x c c' : Nat) : Bool :=
  Nat.beq (walk T L n [c, c'] x) x

@[expose] noncomputable def invOK (T : Nat → Nat) (m n x : Nat) : Bool :=
  allR (nat_lit 0) m fun g =>
    andB (pairOK T (Nat.add m m) n x (Nat.add g g) (Nat.succ (Nat.add g g)))
      (pairOK T (Nat.add m m) n x (Nat.succ (Nat.add g g)) (Nat.add g g))

@[expose] noncomputable def relsOK (T : Nat → Nat) (L n : Nat) (C : Nat → Nat) (Rc : List (List Nat))
    (x : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih k => andB (Nat.beq (walk T L n r x) (Nat.add x (Nat.shiftLeft (C k) (nat_lit 16))))
      (ih (Nat.succ k))) Rc (nat_lit 0)

@[expose] noncomputable def wordsOK (T : Nat → Nat) (L n : Nat) (W : List (List Nat)) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => andB (Nat.beq (walk T L n w x) x) ih) W

@[expose] noncomputable def pointOK (T : Nat → Nat) (m N n : Nat) (C : Nat → Nat)
    (Rc W : List (List Nat)) (x : Nat) : Bool :=
  andB (rangeOK T m N n x)
    (andB (invOK T m n x)
      (andB (relsOK T (Nat.add m m) n C Rc x) (wordsOK T (Nat.add m m) n W x)))

@[expose] noncomputable def paramsOK (N n : Nat) (C : Nat → Nat) (r : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) N) (andB (Nat.ble N (nat_lit 65536)) (andB (Nat.blt (nat_lit 0) n)
    (allR (nat_lit 0) r fun k => Nat.blt (C k) n)))

end CFSG.KC.Mono

end
