module

public import Certificates.Data.Kernel.S1277K589102

public section

namespace CFSG.KC.L34K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def anyK (N : Nat) (f : Nat → Bool) : Bool := notB (allN N fun i => notB (f i))

@[expose] noncomputable def cntK (N : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (f i))) N

@[expose] noncomputable def pc42 (x y : Nat) : Nat := pcomp 42 6 (mask 6) x y

@[expose] noncomputable def inConjK (N : Nat) (E : Nat → Nat) (x k : Nat) : Bool :=
  anyK N fun a => Nat.beq (pc42 x k) (pc42 k (E a))

@[expose] noncomputable def e16K (N : Nat) (E B K : Nat → Nat) (NS : Nat) (ST : Nat → Nat) : Bool :=
  andB (Nat.beq (K 0) (pidn 42 6)) <|
  andB (allN 5 fun i => inK NS ST (K i)) <|
  andB (allN N fun a => inK NS ST (B a)) <|
  andB (allN N fun a => allN N fun b => Nat.beq (pc42 (B a) (B b)) (pc42 (B b) (B a))) <|
  andB (allN N fun a => Nat.beq (pc42 (B a) (B a)) (pidn 42 6)) <|
  andB (Nat.beq (cntK N fun a => inK N E (B a)) 4) <|
  andB (allN N fun b => allN N fun e => anyK N fun y =>
    Nat.beq (pc42 (B b) (E e)) (pc42 (E y) (B b))) <|
  andB (allN N fun b => allN N fun e => anyK N fun y =>
    Nat.beq (pc42 (E e) (B b)) (pc42 (B b) (E y))) <|
  andB (allN 5 fun k => allN N fun b => anyK N fun y =>
    Nat.beq (pc42 (K k) (B b)) (pc42 (B y) (K k))) <|
  andB (allN 5 fun k => allN N fun b => anyK N fun y =>
    Nat.beq (pc42 (B b) (K k)) (pc42 (K k) (B y))) <|
  allN 5 fun i => allN 5 fun j => orB (Nat.beq i j) (allN N fun x =>
    orB (Nat.beq (B x) (pidn 42 6)) (notB (andB (inConjK N E (B x) (K i)) (inConjK N E (B x) (K j)))))

end CFSG.KC.L34K

end
