module

public import Certificates.Data.Kernel.LocalQT.Word

public section

namespace CFSG.KC.LQT.W

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def letZ (n : Nat) (G : List Nat) (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun m => Nat.rec (motive := fun _ => Nat) (inv n (genAt n G 0)) (fun k _ => genAt n G k) m)
    (fun m => inv n (genAt n G m)) z

@[expose] noncomputable def evalZK (n : Nat) (G : List Nat) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (one n) (fun z _ ih => mul n (letZ n G z) ih) w

@[expose] noncomputable def outerC (n cr : Nat) (G : List Nat) (ks : List (List Int)) (w : List Int) :
    Bool :=
  andB (Nat.ble n 32) (andB (Nat.beq (List.rec (motive := fun _ => Nat) 0
      (fun _ _ ih => Nat.succ ih) ks) 3)
    (letB (evalZK n (List.map (fun k =>
        mul n cr (mul n (mul n (evalZK n G k) cr) (inv n (evalZK n G k)))) ks) w) fun z =>
      andB (Nat.beq (pow n z 11) (one n)) (notB (Nat.beq z (one n)))))

end CFSG.KC.LQT.W

end
