module

public import Certificates.Data.Kernel.ThCent.List

public section

namespace CFSG.KC.ThPump

open CFSG.KC.Th CFSG.KC.ThCent

@[expose] noncomputable def andP (a b : Bool) : Bool := Bool.rec false b a

@[expose] noncomputable def isLet (r : Nat) : Bool :=
  Bool.rec (Bool.rec (Bool.rec (Nat.beq r 115) true (Nat.beq r 114)) true (Nat.beq r 99)) true
    (Nat.beq r 19)

@[expose] noncomputable def letsOK (U : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andP (List.rec (motive := fun _ => Bool) true
      (fun r _ ih' => andP (isLet r) ih') w) ih) U

@[expose] noncomputable def selL (a b c d r : Nat) : Nat :=
  Bool.rec (Bool.rec (Bool.rec d c (Nat.beq r 114)) b (Nat.beq r 99)) a (Nat.beq r 19)

@[expose] noncomputable def vWord (rm : Nat) (F : Nat → Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun v => v)
    (fun r _ ih v => strictF (vecB rm v (F r)) ih) w

@[expose] noncomputable def vWordRev (rm : Nat) (G : Nat → Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun v => v)
    (fun r _ ih v => strictF (ih v) fun x => vecB rm x (G r)) w

@[expose] noncomputable def conjRow (rm : Nat) (F G : Nat → Nat) (T : Nat) (w : List Nat) : Nat :=
  strictF (vWord rm F w 1) fun x => strictF (vecB rm x T) (vWordRev rm G w)

@[expose] noncomputable def rowsOK (rm : Nat) (F G : Nat → Nat) (T : Nat) :
    List (List Nat) → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun D => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) D)
    (fun w _ ih D => List.rec (motive := fun _ => Bool) false
      (fun d D' _ => andP (Nat.beq (conjRow rm F G T w) d) (ih D')) D)

end CFSG.KC.ThPump

end
