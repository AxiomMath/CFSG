module

public import CFSG.Certificates.Kernel.Lie.CT.Core
public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KC.U6F2

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def getLD {α : Type} (x : α) (L : List α) : Nat → α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => x)
    (fun a _ ih i => Nat.rec (motive := fun _ => α) a (fun j _ => ih j) i) L

@[expose] noncomputable def urPairK (d : Nat) (G C : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (idF d)
    (fun s _ ih => strictN ih fun X => strictN (getLD (nat_lit 0) G s) fun g =>
      Nat.lor (mulF d g (fget X (nat_lit 0) (Nat.mul d d)))
        (Nat.shiftLeft (Nat.xor (mulF d g (fget X (nat_lit 1) (Nat.mul d d)))
          (mulF d (getLD (nat_lit 0) C s) (fget X (nat_lit 0) (Nat.mul d d)))) (Nat.mul d d))) w

@[expose] noncomputable def trK (d X : Nat) : Nat :=
  strictN X fun X => orN d fun i => orN d fun j =>
    nIf(bit X (Nat.add (Nat.mul d j) i), pw2 (Nat.add (Nat.mul d i) j), nat_lit 0)

@[expose] noncomputable def msumK (k mask : Nat) (F : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun m acc => nIf(bit mask m, Nat.xor (F m) acc, acc)) k

@[expose] noncomputable def rowMulK (a : Nat) (B : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun b _ ih a acc => strictN (nIf(bit a (nat_lit 0), Nat.xor acc b, acc)) fun acc =>
      ih (Nat.shiftRight a (nat_lit 1)) acc) B a (nat_lit 0)

@[expose] noncomputable def idRowsAux (n : Nat) (B Q : List Nat) : List Nat → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool)
    (fun E l => andB (Nat.beq l n) (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) E))
    (fun f _ ih E l => List.rec (motive := fun _ => Bool) false
      (fun e E' _ => andB
        (Nat.beq (Nat.land (Nat.xor (rowMulK e B) (rowMulK f Q)) (maskN n)) (pw2 l))
        (ih E' (Nat.succ l))) E)

@[expose] noncomputable def idRowsSeg (n : Nat) (B Q : List Nat) : List Nat → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool)
    (fun E _ => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) E)
    (fun f _ ih E l => List.rec (motive := fun _ => Bool) false
      (fun e E' _ => andB
        (Nat.beq (Nat.land (Nat.xor (rowMulK e B) (rowMulK f Q)) (maskN n)) (pw2 l))
        (ih E' (Nat.succ l))) E)

@[expose] noncomputable def idRowsK (n : Nat) (F E B Q : List Nat) : Bool :=
  idRowsAux n B Q F E (nat_lit 0)

end CFSG.KC.U6F2

end
