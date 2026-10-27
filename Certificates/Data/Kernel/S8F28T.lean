module

public import Certificates.Data.Kernel.S8F28K
public import CFSG.Quasithin.Vol2.Ch12Sec6S8Data28

public section

namespace CFSG.KC.S8F28K

open CFSG.KC.Enum CFSG.Quasithin.H13 S8E S8F

@[expose] noncomputable def fixB (f u : List Nat) : Bool :=
  id8.all (fun i => ap u (ap f i) == ap u i) || id8.all fun i => !(ap u (ap f i) == ap u i)

@[expose] noncomputable def vecB (u : List Nat) : Bool :=
  id8.all (fun i => Nat.blt (ap u i) 2) &&
    (ap u 0 + ap u 1 + ap u 2 + ap u 3 + ap u 4 + ap u 5 + ap u 6 + ap u 7) % 2 == 0

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

@[expose] noncomputable def tabFix (FMK a : Nat) : Bool :=
  allN 128 fun v => fixB (iv a) (VECS.getD v []) == (fk FMK a).testBit v

@[expose] noncomputable def tabVec : Bool := allN 128 fun v => vecB (VECS.getD v [])

end CFSG.KC.S8F28K
