module

public import Certificates.Data.Kernel.PGrp
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.U38QK

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def allL (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) L

@[expose] noncomputable def pairK (f : Nat → Nat → Bool) (I : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun J => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) J)
    (fun i _ ih J => List.rec (motive := fun _ => Bool) false (fun j js _ => bAnd(f i j, ih js)) J) I

@[expose] noncomputable def selL (q : Nat → Bool) (L : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun S => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) S)
    (fun x _ ih S => bIf(q x,
      List.rec (motive := fun _ => Bool) false (fun y ys _ => bAnd(Nat.beq y x, ih ys)) S,
      ih S)) L

@[expose] noncomputable def cubeK (n w a : Nat) : Bool :=
  Nat.beq (pcomp n w (mask w) a (pcomp n w (mask w) a a)) (pidn n w)

@[expose] noncomputable def noCommK (n w : Nat) (ps : List Nat) (T : Nat → Nat) (A B : List Nat) :
    Bool :=
  allL (fun a => strictB (T a) fun x => allL (fun b => strictB (T b) fun y =>
    !(Nat.beq (PGrp.keyCK n w ps x y) (PGrp.keyCK n w ps y x))) B) A

end CFSG.KC.U38QK

end
