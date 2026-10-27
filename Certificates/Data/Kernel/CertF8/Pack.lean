module

public import Certificates.Data.Kernel.G28.Defs

public section

namespace CFSG.KC.CertF8

open CFSG.KC.G28 (fld letN mx idP letterP)

@[expose] noncomputable def spr (a o L F : Nat) : Nat :=
  Nat.mul (Nat.land (Nat.shiftRight a o) L) F

@[expose] noncomputable def termsL (a k e W L F : Nat) (Xs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun X _ ih b => Nat.xor
      (Nat.land (spr a (Nat.add (Nat.mul e k) b) L F) (Nat.mul (fld X (Nat.mul W k) W) L))
      (ih (Nat.succ b))) Xs

@[expose] noncomputable def mulG (n e W L F a : Nat) (Xs : List Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.xor acc (termsL a k e W L F Xs 0)) n

@[expose] def L6 : Nat := 1237944761669877611773558785

@[expose] def F18 : Nat := 262143

@[expose] noncomputable def mulS6 (a b : Nat) : Nat :=
  letN a fun a => letN b fun b => letN (mx b) fun b1 => letN (mx b1) fun b2 =>
    mulG 6 3 18 L6 F18 a [b, b1, b2]

@[expose] noncomputable def wordS6 (w : List Nat) : Nat :=
  w.foldl (fun A n => mulS6 A (letterP n)) idP

@[expose] noncomputable def powS6 (A : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idP (fun _ acc => mulS6 acc A) k

end CFSG.KC.CertF8

end
