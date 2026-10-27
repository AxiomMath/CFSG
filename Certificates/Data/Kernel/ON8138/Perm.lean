module

public import Certificates.Data.Kernel.ON8138.Defs

public section

namespace CFSG.KC.ON8138

@[expose] noncomputable def pd (c i : Nat) : Nat := Nat.mod (Nat.div c (Nat.pow (nat_lit 8) i)) (nat_lit 8)

@[expose] noncomputable def pcomp (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.mul (pd a (pd b i)) (Nat.pow (nat_lit 8) i))) (nat_lit 6)

@[expose] noncomputable def pid : Nat := nat_lit 181896

@[expose] noncomputable def ppow (c k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) pid (fun _ acc => pcomp acc c) k

@[expose] noncomputable def pevW (x y : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) pid (fun l _ ih => pcomp (Bool.rec y x (Nat.beq l (nat_lit 0))) ih) w

@[expose] noncomputable def a6OK (P : Nat → Nat) (y0 y1 t4 k1 k2 : Nat) (w0 w1 w4 : List Nat) : Bool :=
  allK (nat_lit 81) fun i => allK (nat_lit 81) fun j => strictN (P i) fun x => strictN (P j) fun y =>
    orK (notK (Nat.beq (ppow (pcomp x y) (nat_lit 5)) pid))
      (orK (notK (Nat.beq (pevW x y w0) y0))
        (orK (notK (Nat.beq (pevW x y w1) y1))
          (orK (notK (Nat.beq (pevW x y w4) t4)) (andK (Nat.beq x k1) (Nat.beq y k2)))))

end CFSG.KC.ON8138

end
