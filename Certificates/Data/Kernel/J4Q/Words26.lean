module

public import Certificates.Data.Kernel.J4Q.Mat

public section

namespace CFSG.KC.J4Q

open CFSG.KC.Loop

@[expose] noncomputable def letAZ (k : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.neg (Int.ofNat (Nat.sub k (nat_lit 64))))
    (Int.ofNat (Nat.sub k (nat_lit 96))) (Nat.ble (nat_lit 97) k)

@[expose] noncomputable def lettersAZ (cs : List Char) : List Int :=
  List.rec (motive := fun _ => List Int) List.nil
    (fun ch _ ih => List.cons (letAZ (Char.toNat ch)) ih) cs

@[expose] noncomputable def wordVJ (rm one : Nat) (mats invs : List Nat) (w : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => strictN (vecJ rm x (letJ one mats invs l)) ih) w

end CFSG.KC.J4Q

end
