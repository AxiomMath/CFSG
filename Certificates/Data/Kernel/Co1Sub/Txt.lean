module

public import Certificates.Data.Kernel.Griess13.Packed

public section

namespace CFSG.KC.Co1Sub

open CFSG.KC.G13

@[expose] noncomputable def decZ (c : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.ofNat (Nat.succ (Nat.div c (nat_lit 2))))
    (Int.negSucc (Nat.div c (nat_lit 2))) (Nat.beq (Nat.mod c (nat_lit 2)) (nat_lit 1))

@[expose] noncomputable def wordC (w : List Nat) : List Char :=
  [','].intercalate (w.map fun c => intC (decZ c))

@[expose] noncomputable def wordsC (W : List (List Nat)) : List Char :=
  [';'].intercalate (W.map wordC)

@[expose] noncomputable def nonemptyK (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => Bool.rec (motive := fun _ => Bool) false ih
      (List.rec (motive := fun _ => Bool) false (fun _ _ _ => true) w)) W

end CFSG.KC.Co1Sub

end
