module

public import Certificates.Data.Kernel.BfsTreeK

public section

namespace CFSG.KC.BfsT

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2

@[expose] noncomputable def minK (a b : Nat) : Nat := nIf(Nat.ble a b, a, b)

@[expose] noncomputable def canonK (x y v : Nat) : Nat :=
  minK (minK v (Nat.xor v x)) (minK (Nat.xor v y) (Nat.xor (Nat.xor v x) y))

@[expose] noncomputable def lettersC (x0 y0 : Nat) (L P B : List Nat) (n x h : Nat) (Ms : List Nat) :
    Nat → Nat → (Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → Nat → (Nat → Bool) → Bool) (fun _ c k => k c)
    (fun M _ ih l c k => strictB l fun l => strictB c fun c =>
      strictB (canonK x0 y0 (vmF 24 M x)) fun w =>
        andB (Nat.blt w (pw2 24))
          (bIf(preK L c w, ih (Nat.succ l) c k,
            andB (andB (Nat.blt c n) (Nat.beq (getL 0 L c) w))
              (andB (andB (Nat.beq (getL 0 P c) h) (Nat.beq (getL 0 B c) l))
                (ih (Nat.succ l) (Nat.succ c) k))))) Ms

@[expose] noncomputable def runC (Ms : List Nat) (x0 y0 cap : Nat) (L P B : List Nat) (n : Nat)
    (xs : List Nat) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ c => Nat.beq c n)
    (fun x _ ih h c => strictB h fun h => strictB c fun c =>
      bIf(andB (Nat.blt h cap) (Nat.blt h c),
        lettersC x0 y0 L P B n x h Ms 0 c fun c => ih (Nat.succ h) c,
        Nat.beq c n)) xs

@[expose] noncomputable def cbfsK (Ms : List Nat) (x0 y0 c0 cap : Nat) (L P B : List Nat) : Bool :=
  strictB (lenL L) fun n =>
    andB (andB (andB (Nat.blt 0 n) (Nat.blt c0 (pw2 24)))
        (andB (Nat.beq (lenL P) n) (Nat.beq (lenL B) n)))
      (andB (andB (Nat.beq (getL 0 L 0) c0) (andB (Nat.beq (getL 0 P 0) 0) (Nat.beq (getL 0 B 0) 0)))
        (runC Ms x0 y0 cap L P B n L 0 1))

end CFSG.KC.BfsT

end
