module

public import Certificates.Data.Kernel.ThCensus.Defs

public section

namespace CFSG.KC.ThCensus

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Loop

@[expose] noncomputable def letR (r0 r1 r2 r3 x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) r3 r2 (Nat.beq x (nat_lit 2))) r1 (Nat.beq x (nat_lit 1)))
    r0 (Nat.beq x (nat_lit 0))

@[expose] noncomputable def wordR (RB : Nat → Nat) (c rm r0 r1 r2 r3 : Nat) (n : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => strictN (mulB c rm S (RB (letR r0 r1 r2 r3 (Nat.land J (nat_lit 3)))))
      (ih (Nat.shiftRight J (nat_lit 2)))) n

@[expose] noncomputable def nfOK (l : List Nat) : Bool :=
  andB (Nat.beq (lenN l) (nat_lit 10))
    (List.rec (motive := fun _ => Bool) true (fun e _ ih => andB (Nat.blt e (nat_lit 3)) ih) l)

@[expose] noncomputable def nfsOK (L : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ ih => andB (nfOK l) ih) L

@[expose] noncomputable def nfX (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e _ acc => Nat.lor e (Nat.shiftLeft acc (nat_lit 2))) l

@[expose] noncomputable def nfM (PW : Nat → Nat) (c rm ONE : Nat) (l : List Nat) : Nat :=
  rhsPc PW c rm ONE (nat_lit 10) (nat_lit 3) (nat_lit 2) (nfX l)

@[expose] noncomputable def conjEq (c rm X Y W : Nat) : Bool :=
  Nat.beq (nat_lit 1) (strictN W (fun W => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
    (Nat.beq (mulB c rm W X) (mulB c rm Y W))))

@[expose] noncomputable def fusOK (RB PW : Nat → Nat) (c rm ONE r2 r3 : Nat) (reps tgts : List (List Nat))
    (e : List Nat) (w : Nat) : Bool :=
  conjEq c rm (nfM PW c rm ONE (reps.getD (e.getD 0 0) [])) (nfM PW c rm ONE (tgts.getD (e.getD 1 0) []))
    (wordR RB c rm (nat_lit 1) (nat_lit 2) r2 r3 (e.getD 2 0) w ONE)

@[expose] noncomputable def clsM (RB : Nat → Nat) (c rm rz rs ru k : Nat) : Nat :=
  (fun r => Bool.rec (motive := fun _ => Nat) (mulB c rm (RB r) (RB r)) (RB r)
      (Nat.beq (Nat.land k (nat_lit 1)) (nat_lit 0)))
    (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) ru rs (Nat.blt k (nat_lit 4))) rz
      (Nat.blt k (nat_lit 2)))

@[expose] noncomputable def cenOK (RB PW : Nat → Nat) (c rm ONE r2 rz rs ru : Nat) (T : List Nat)
    (e : List Nat) (w : Nat) : Bool :=
  andB (Nat.blt (e.getD 0 0) (nat_lit 6))
    (conjEq c rm (nfM PW c rm ONE T) (clsM RB c rm rz rs ru (e.getD 0 0))
      (wordR RB c rm (nat_lit 1) (nat_lit 2) r2 (nat_lit 0) (e.getD 1 0) w ONE))

@[expose] noncomputable def fusIdxOK (nr nt : Nat) (F : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => andB (andB (Nat.beq (lenN e) (nat_lit 3))
      (andB (Nat.blt (e.getD 0 0) nr) (Nat.blt (e.getD 1 0) nt))) ih) F

@[expose] noncomputable def anyL {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => orB (p a) ih) l

@[expose] noncomputable def coverOK (reps tgts F : List (List Nat)) (nr : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih
    (orB (anyL (fun e => Nat.beq (e.getD 0 0) i) F)
      (anyL (fun t => Nat.beq (nfX t) (nfX (reps.getD i []))) tgts))) nr

end CFSG.KC.ThCensus

end
