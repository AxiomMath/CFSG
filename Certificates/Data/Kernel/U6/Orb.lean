module

public import Certificates.Data.Kernel.U6.Abar

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def mapM (M k v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc fun acc =>
      nIf(Nat.beq (fget v i (nat_lit 1)) (nat_lit 1),
        Nat.xor acc (fget M (Nat.add (Nat.mul (nat_lit 9) k) i) (nat_lit 9)), acc))
    (nat_lit 9)

@[expose] noncomputable def stepS (M n S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S
    (fun x acc => strictN acc fun acc =>
      nIf(Nat.beq (fget S x (nat_lit 1)) (nat_lit 1),
        Nat.rec (motive := fun _ => Nat) acc
          (fun k acc' => strictN acc' fun acc' => Nat.lor acc' (pw2 (mapM M k x))) n,
        acc))
    (nat_lit 512)

@[expose] noncomputable def closeS (M n S r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S (fun _ T => strictN T fun T => stepS M n T) r

@[expose] noncomputable def closedK (M n S : Nat) : Bool :=
  allBelow (nat_lit 512) (nat_lit 8) fun x =>
    orB (Nat.beq (fget S x (nat_lit 1)) (nat_lit 0))
      (allN n fun k => Nat.beq (fget S (mapM M k x) (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def popK (S : Nat) : Nat :=
  sumBelow (nat_lit 512) (nat_lit 8) fun x => fget S x (nat_lit 1)

@[expose] noncomputable def orbK (M n : Nat) : Bool :=
  strictB (closeS M n (pw2 (nat_lit 1)) (nat_lit 12)) fun S1 =>
  strictB (closeS M n (pw2 (nat_lit 18)) (nat_lit 12)) fun S2 =>
  strictB (closeS M n (pw2 (nat_lit 19)) (nat_lit 12)) fun S3 =>
    andB (andB (closedK M n S1) (andB (closedK M n S2) (closedK M n S3)))
      (andB (andB (Nat.beq (popK S1) (nat_lit 21))
          (andB (Nat.beq (popK S2) (nat_lit 210)) (Nat.beq (popK S3) (nat_lit 280))))
        (Nat.beq (Nat.lor S1 (Nat.lor S2 S3)) (Nat.sub (pw2 (nat_lit 512)) (nat_lit 2))))

end CFSG.KC.U6

end
