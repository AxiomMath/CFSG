module

public import Certificates.Data.Kernel.WeylE8.Frame

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum

@[expose] noncomputable def spAt (g j : Nat) : Nat := pg (nat_lit 3) (nat_lit 7) g j

@[expose] noncomputable def spMask (g : Nat) : Nat := Nat.land (Nat.shiftRight g (nat_lit 24)) (nat_lit 255)

@[expose] noncomputable def spImgMask (g m : Nat) : Nat :=
  sumN (nat_lit 8) fun j =>
    nIf(Nat.beq (Nat.land (Nat.shiftRight m j) (nat_lit 1)) (nat_lit 1),
      Nat.shiftLeft (nat_lit 1) (spAt g j), nat_lit 0)

@[expose] noncomputable def spMul (g h : Nat) : Nat :=
  Nat.add (sumN (nat_lit 8) fun j => Nat.shiftLeft (spAt g (spAt h j)) (Nat.mul (nat_lit 3) j))
    (Nat.shiftLeft (Nat.land (Nat.xor (spMask g) (spImgMask g (spMask h))) (nat_lit 255)) (nat_lit 24))

@[expose] noncomputable def spId : Nat := nat_lit 16434824

end CFSG.KLC.E8

end
