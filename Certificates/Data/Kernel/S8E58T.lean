module

public import Certificates.Data.Kernel.S8E58K
public import CFSG.Quasithin.Vol2.Ch12Sec6S8Data

public section

namespace CFSG.KC.S8E58K

open CFSG.KC.Enum CFSG.Quasithin.H13 S8E

@[expose] noncomputable def halvesB (f : List Nat) : Bool :=
  [0, 1, 2, 3].all (fun i => Nat.blt (ap f i) 4) || [0, 1, 2, 3].all fun i => Nat.ble 4 (ap f i)

@[expose] noncomputable def k0B : Bool :=
  id8.all fun a => id8.all fun b => id8.all fun c => id8.all fun d =>
    !(cmp (ext4 a b c d) (ext4 a b c d) == id8) || !(halvesB (ext4 a b c d)) ||
      ext4 a b c d == id8 || INV.contains (ext4 a b c d)

@[expose] noncomputable def tabCM (CM MT : Nat) : Bool :=
  allN 44 fun a => allN 44 fun b =>
    ((cmp (iv a) (iv b) == cmp (iv b) (iv a)) == cm CM a b) &&
      (!(cm CM a b) || (Nat.blt (mt MT a b) 44 && cmp (iv a) (iv b) == iv (mt MT a b))) &&
      (!(iv a == iv b) || Nat.beq a b)

@[expose] noncomputable def tabFX (FX : Nat) : Bool :=
  allN 44 fun a => allN 8 fun p => (ap (iv a) p == p) == (fx FX a).testBit p

end CFSG.KC.S8E58K
