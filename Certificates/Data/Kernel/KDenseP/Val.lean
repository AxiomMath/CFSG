module

public import Certificates.Data.Kernel.KDenseP.Letters

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.KDense

@[expose] noncomputable def resAt (S n x p : Nat) : Nat :=
  Nat.mod (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun b acc => Nat.add acc (Nat.shiftLeft (bitN x (Nat.add (Nat.mul b S) p)) b)) n)
    (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1))

@[expose] noncomputable def trRes (n A : Nat) : Nat :=
  Nat.mod (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.rec (motive := fun _ => Nat) acc
        (fun j acc2 => (fun r => Nat.add acc2 (Nat.mul r r))
          (resAt SA n A (Nat.add (Nat.mul (nat_lit 32) i) j))) (nat_lit 24)) (nat_lit 24))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1))

@[expose] noncomputable def valOK (n : Nat) (s : St) (t u : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun f r => Prod.rec (motive := fun _ => Bool) (fun X r2 =>
    Prod.rec (motive := fun _ => Bool) (fun A _ =>
      andB f (andB (Nat.beq (trRes n A) t) (Nat.beq (resAt SX n X (nat_lit 114689)) u))) r2) r) s

end CFSG.KC.KDenseP

end
