module

public import Certificates.Data.Kernel.SporSch.Co1MatW
public import Certificates.Data.Kernel.Spor.Mathieu

public section

namespace CFSG.KS.Co1Row26683M

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KS.Mathieu

@[expose] noncomputable def mW (A B : Nat) : Nat := CFSG.KC.Co1B.mulWK A B

@[expose] noncomputable def encW (w : List Int) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun z _ ih => List.cons (icode z) ih) w

@[expose] noncomputable def encWL (ws : List (List Int)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) [] (fun w _ ih => List.cons (encW w) ih) ws

@[expose] noncomputable def prodIdxK (M : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun i _ ih acc => strictN (mW acc (M i)) ih) w idM

@[expose] noncomputable def allLtK (n : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun i _ ih => bAnd(Nat.blt i n, ih)) w

@[expose] noncomputable def conjK (L A Li : Nat) : Nat := mW (mW L A) Li

@[expose] noncomputable def matK (X Y P₁ P₂ : Nat) (ZM ZMI LM LMI HM HMI : Nat → Nat)
    (wZ wL : List Int) (wH : List (List Int)) (W1 W2 : List Nat) (v : Nat) : Bool :=
  strictB (mW (mW X Y) X) fun B => strictB (ZM (nat_lit 2)) fun Z =>
  strictB (LM (nat_lit 2)) fun L => strictB (LMI (nat_lit 2)) fun Li =>
  bAnd(Nat.beq (mW X X) idM,
  bAnd(Nat.beq (mW (mW (mW (mW Y Y) Y) Y) Y) idM,
  bAnd(Nat.beq (ZM (nat_lit 0)) Y, bAnd(Nat.beq (ZM (nat_lit 1)) B,
  bAnd(dagWK ZM ZMI (nat_lit 2) (nat_lit 3) [encW wZ],
  bAnd(Nat.beq (mW Z Z) idM, bAnd(Bool.not (Nat.beq Z idM),
  bAnd(Nat.beq (LM (nat_lit 0)) P₁, bAnd(Nat.beq (LM (nat_lit 1)) P₂,
  bAnd(dagWK LM LMI (nat_lit 2) (nat_lit 3) [encW wL],
  bAnd(Nat.beq (conjK L P₁ Li) (mW P₁ Z),
  bAnd(Nat.beq (HM (nat_lit 0)) Y, bAnd(Nat.beq (HM (nat_lit 1)) B,
  bAnd(Nat.beq (HM (nat_lit 2)) (conjK L Y Li), bAnd(Nat.beq (HM (nat_lit 3)) (conjK L B Li),
  bAnd(dagWK HM HMI (nat_lit 4) (nat_lit 12) (encWL wH),
  bAnd(allLtK (nat_lit 12) W1, bAnd(allLtK (nat_lit 12) W2,
  bAnd(Nat.beq (prodIdxK HM W1) P₁, bAnd(Nat.beq (prodIdxK HM W2) P₂,
  Nat.beq (actK Z v) v))))))))))))))))))))

end CFSG.KS.Co1Row26683M

end
