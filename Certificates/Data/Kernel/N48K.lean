module

public import Certificates.Data.Kernel.HexaStabK

public section

namespace CFSG.KC.N48K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.HexaK CFSG.KC.HexaStabK
open CFSG.KLie.CT (anyN sumN andB orB notB pw2 bit)

@[expose] noncomputable def invL (w NN : Nat) (TN : Nat → Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun r ih acc => (fun a => Bool.rec (motive := fun _ => List Nat) (ih acc) (ih (a :: acc))
      (Nat.beq (mul 64 w a a) (pidn 64 w))) (TN r)) NN []

@[expose] noncomputable def fixM (w a b : Nat) : Nat :=
  sumN 64 fun c => Bool.rec (motive := fun _ => Nat) 0 (pw2 c)
    (andB (Nat.beq (pgC 64 w a c) c) (Nat.beq (pgC 64 w b c) c))

@[expose] noncomputable def cntM (S : Nat) : Nat := popK 64 S

@[expose] noncomputable def shiftM (C x : Nat) : Nat :=
  sumN 64 fun w => Bool.rec (motive := fun _ => Nat) 0 (pw2 w) (bit C (Nat.xor w x))

@[expose] noncomputable def spanM (w a b C : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) C (fun v acc => strictN acc fun acc =>
    Nat.lor acc (Nat.lor (shiftM C (Nat.xor v (pgC 64 w a v)))
      (Nat.lor (shiftM C (Nat.xor v (pgC 64 w b v)))
        (shiftM C (Nat.xor v (pgC 64 w a (pgC 64 w b v))))))) 64

@[expose] noncomputable def fourK (w a b C S : Nat) : Bool :=
  andB (orB (Nat.ble 16 (cntM (fixM w a a))) (orB (Nat.ble 16 (cntM (fixM w b b)))
      (strictB (mul 64 w a b) fun ab => Nat.ble 16 (cntM (fixM w ab ab)))))
    (orB (Nat.blt (cntM S) 16) (andB (Nat.ble (cntM C) 4)
      (anyN 64 fun x => andB (notB (bit S x))
        (orB (bit C (Nat.xor x (pgC 64 w a x))) (orB (bit C (Nat.xor x (pgC 64 w b x)))
          (bit C (Nat.xor x (pgC 64 w a (pgC 64 w b x)))))))))

@[expose] noncomputable def pairK (w a b : Nat) : Bool :=
  strictB (fixM w a b) fun C => strictB (spanM w a b C) fun S =>
    orB (notB (comm 64 w a b)) (orB (andB (Nat.beq a (pidn 64 w)) (Nat.beq b (pidn 64 w)))
      (andB (Nat.ble (cntM S) 16) (orB (Nat.beq a (pidn 64 w)) (orB (Nat.beq b (pidn 64 w))
        (orB (Nat.beq a b) (fourK w a b C S))))))

@[expose] noncomputable def rankK (w : Nat) (I : List Nat) : Bool :=
  I.all fun a => I.all fun b => I.all fun c =>
    orB (notB (comm 64 w a b)) (orB (notB (comm 64 w a c)) (orB (notB (comm 64 w b c))
      (orB (Nat.beq a (pidn 64 w)) (orB (Nat.beq b (pidn 64 w)) (orB (Nat.beq b a)
        (orB (Nat.beq c (pidn 64 w)) (orB (Nat.beq c a) (orB (Nat.beq c b)
          (Nat.beq c (mul 64 w a b))))))))))

@[expose] noncomputable def rankRowK (w : Nat) (I : List Nat) (i : Nat) : Bool :=
  strictB (I.getD i 0) fun a => I.all fun b => I.all fun c =>
    orB (notB (comm 64 w a b)) (orB (notB (comm 64 w a c)) (orB (notB (comm 64 w b c))
      (orB (Nat.beq a (pidn 64 w)) (orB (Nat.beq b (pidn 64 w)) (orB (Nat.beq b a)
        (orB (Nat.beq c (pidn 64 w)) (orB (Nat.beq c a) (orB (Nat.beq c b)
          (Nat.beq c (mul 64 w a b))))))))))

@[expose] noncomputable def pairRowK (w : Nat) (I : List Nat) (i : Nat) : Bool :=
  strictB (I.getD i 0) fun a => I.all fun b => pairK w a b

end CFSG.KC.N48K

end
