module

public import Certificates.Data.Kernel.SlpPcCl

public section

namespace CFSG.KC.SlpPc

open CFSG.KC.Ord

@[expose] noncomputable def pw1 (mul : Nat → Nat → Nat) (X n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X (fun _ acc => mul acc X) n

@[expose] noncomputable def trL (w S d X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (bitsN X (Nat.add (Nat.mul S i) (Nat.mul w i)) w)) d

@[expose] noncomputable def rowOK (mul : Nat → Nat → Nat) (n : Nat) (tv : List Nat) (t : Nat)
    (sv : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun g _ ih c => andB (Nat.blt (nthD 0 c 0) n)
      (andB (Nat.beq (mul t g) (nthD 0 tv (nthD 0 c 0))) (ih (tl c)))) sv

@[expose] noncomputable def itN (cb : List Nat) (k i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) i (fun _ j => nthD 0 cb j) k

@[expose] noncomputable def tabOK (mul : Nat → Nat → Nat) (p k n : Nat) (tv sv : List Nat)
    (cl : List (List Nat)) (cb : List Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun t _ ih i => andB (rowOK mul n tv t sv (nthD List.nil cl i))
      (andB (Nat.blt (nthD 0 cb i) n)
        (andB (Nat.beq (pw1 mul t (Nat.sub p 1)) (nthD 0 tv (nthD 0 cb i)))
          (andB (Nat.beq (itN cb k i) 0) (ih (Nat.succ i)))))) l

@[expose] noncomputable def entsOK (mul : Nat → Nat → Nat) (ONE : Nat) (R : Nat → Nat)
    (sv : List Nat) (X : Nat) (es : List (Nat × (List Nat × List Nat))) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => andB (sB (wordP mul ONE (nthD ONE sv) e.2.1) fun y => sB (R e.1) fun H =>
      andB (Nat.beq (mul X H) (mul H y)) (commOK mul R y e.2.2)) ih) es

@[expose] noncomputable def zsE (es : List (Nat × (List Nat × List Nat))) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun e _ ih => revOnto (revOnto e.2.2 List.nil) ih) es

@[expose] noncomputable def clsL (mul : Nat → Nat → Nat) (ONE A B p q k t w S d : Nat)
    (prg : List (Nat × Nat)) (rx : Nat) (sg tb : List Nat) (cl : List (List Nat)) (cb : List Nat)
    (ent : List (Nat × (List Nat × List Nat))) (lp : List (Nat × Nat)) (ab : List Nat) : Bool :=
  runP mul ONE prg List.nil [B, A, ONE] 3 fun bl cur n =>
    sB (lk ONE bl cur n rx) fun X =>
    mapS (lk ONE bl cur n) sg fun sv =>
    mapS (lk ONE bl cur n) tb fun tv =>
    mapS (lk ONE bl cur n) (zsE ent) fun zv =>
      andB (notB (Nat.beq X ONE)) (andB (Nat.beq (pw1 mul X (Nat.sub p 1)) ONE)
        (andB (Nat.beq (Nat.mod (trL w S d X) q) t) (andB (Nat.beq (nthD 0 tv 0) ONE)
          (andB (tabOK mul p k (lenN tv) tv sv cl cb tv 0)
            (andB (entsOK mul ONE (lk ONE bl cur n) sv X ent)
              ((fun cur0 => runP mul ONE lp List.nil cur0 (lenN cur0) fun bl' cur' n' =>
                  andB (Nat.beq (lk ONE bl' cur' n' (nthD 0 ab 0)) A)
                    (Nat.beq (lk ONE bl' cur' n' (nthD 0 ab 1)) B))
                (revOnto zv (revOnto sv [ONE]))))))))

end CFSG.KC.SlpPc

end
