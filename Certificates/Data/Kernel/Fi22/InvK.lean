module

public import Certificates.Data.Kernel.Fi22.Letters

public section

namespace CFSG.KS.Fi22I

open CFSG.KC.Enum CFSG.KS.Fi22L

@[expose] def ilText : String := include_str "invl.hex"

@[expose] noncomputable def ilPacked : Nat := by hex_nat ilText 786384 14506086822188317182

@[expose] def irText : String := include_str "invr.hex"

@[expose] noncomputable def irPacked : Nat := by hex_nat irText 430 18437346835264711820

@[expose] noncomputable def ilRow (k : Nat) : Nat :=
  Nat.land (Nat.shiftRight ilPacked (Nat.mul (nat_lit 3072) k)) (wM (nat_lit 3072))

@[expose] noncomputable def ilE (k j : Nat) : Nat :=
  Nat.land (Nat.shiftRight (ilRow k) (Nat.mul (nat_lit 24) j)) (nat_lit 16777215)

@[expose] noncomputable def ilR (k j : Nat) : Nat := Nat.shiftRight (ilE k j) (nat_lit 17)

@[expose] noncomputable def ilK (k j : Nat) : Nat := Nat.land (ilE k j) (nat_lit 1023)
@[expose] noncomputable def ilJ (k j : Nat) : Nat :=
  Nat.land (Nat.shiftRight (ilE k j) (nat_lit 10)) (nat_lit 127)

@[expose] noncomputable def rpK (r : Nat) : Nat :=
  Nat.land (Nat.shiftRight irPacked (Nat.mul (nat_lit 32) r)) (nat_lit 1023)
@[expose] noncomputable def rpJ (r : Nat) : Nat :=
  Nat.land (Nat.shiftRight irPacked (Nat.add (Nat.mul (nat_lit 32) r) (nat_lit 10))) (nat_lit 127)
@[expose] noncomputable def rpC (r : Nat) : Nat :=
  Nat.land (Nat.shiftRight irPacked (Nat.add (Nat.mul (nat_lit 32) r) (nat_lit 17))) (nat_lit 1023)

end CFSG.KS.Fi22I

end
