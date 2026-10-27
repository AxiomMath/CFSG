module

public import Certificates.Data.Kernel.Co1F2

public section

namespace CFSG.KC.BfsT

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2

@[expose] noncomputable def preK (L : List Nat) (c w : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun y _ ih c => Nat.rec (motive := fun _ => Bool) false (fun c' _ => orB (Nat.beq y w) (ih c')) c)
    L c

@[expose] noncomputable def stepK (f : Nat → Nat → Nat) (L P B : List Nat) (n x h l c : Nat)
    (k : Nat → Bool) : Bool :=
  strictB (f l x) fun w =>
    bIf(preK L c w, k c,
      andB (andB (Nat.blt c n) (Nat.beq (getL 0 L c) w))
        (andB (andB (Nat.beq (getL 0 P c) h) (Nat.beq (getL 0 B c) l)) (k (Nat.succ c))))

@[expose] noncomputable def runK (f : Nat → Nat → Nat) (L P B : List Nat) (n : Nat) (xs : List Nat) :
    Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ c => Nat.beq c n)
    (fun x _ ih h c => strictB h fun h => strictB c fun c =>
      andB (Nat.blt h c) (stepK f L P B n x h 0 c fun c =>
        stepK f L P B n x h 1 c fun c => ih (Nat.succ h) c)) xs

@[expose] noncomputable def bfsK (f : Nat → Nat → Nat) (w0 cap : Nat) (L P B : List Nat) : Bool :=
  strictB (lenL L) fun n =>
    andB (andB (andB (Nat.blt 0 n) (Nat.ble n cap)) (andB (Nat.beq (lenL P) n) (Nat.beq (lenL B) n)))
      (andB (andB (Nat.beq (getL 0 L 0) w0) (andB (Nat.beq (getL 0 P 0) 0) (Nat.beq (getL 0 B 0) 0)))
        (runK f L P B n L 0 1))

@[expose] noncomputable def wordFA (A B : Nat) (w : List Bool) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun b _ ih acc => strictN (mulF 24 acc (Bool.rec (motive := fun _ => Nat) B A b)) ih) w

@[expose] noncomputable def wordF (A B : Nat) (w : List Bool) : Nat := wordFA A B w (idF 24)

@[expose] noncomputable def gwFA (K : List Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (mulF 24 acc (getL 0 K l)) ih) w

@[expose] noncomputable def gwF (K : List Nat) (w : List Nat) : Nat := gwFA K w (idF 24)

end CFSG.KC.BfsT

end
