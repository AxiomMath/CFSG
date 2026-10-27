module

public import Certificates.Data.Kernel.F4Syl3Rel

public section

namespace CFSG.KC.F4Syl3

open CFSG.LieType.Simplicity.TitsBits CFSG.KC.F4Salt CFSG.KC.Loop

@[expose] def flipC (c : Nat) : Nat := if c < 4 then 3 - c else 11 - c

@[expose] def rBBits : Nat := mul (sBits 0) (sBits 1)

@[expose] def rhoBits (j : Nat) : Nat := if j = 0 then sBits 3 else rBBits

@[expose] def invT (i : Nat) : Nat :=
  if i = 0 then pack (eltBits 43) else if i = 1 then pack (eltBits 44) else
    if i = 2 then mul (pack (eltBits 43)) (pack (eltBits 44)) else
      mul (pack (eltBits 36)) (pack (eltBits 35))

@[expose] def allN (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun m ih => p m && ih) n

@[expose] noncomputable def flipOK (W Wf L : Nat) : Bool :=
  allN L fun m => digit Wf m == flipC (digit W m)

@[expose] noncomputable def revOK (W Wr L : Nat) : Bool :=
  allN L fun m => digit Wr m == digit W (L - 1 - m)

@[expose] noncomputable def phiN (wA L wAf cB L' : Nat) : Nat :=
  (flipOK wA wAf L).toNat *
  strictN (wordS wA L) fun A => strictN (wordS wAf L) fun F => strictN (wordS cB L') fun C =>
    (eqS A (saltOf (sBits 3)) && eqS (mulS C F) (mulS (saltOf rBBits) C)).toNat

@[expose] noncomputable def invN (k W L Wr : Nat) : Nat :=
  (revOK W Wr L).toNat *
  strictN (wordS W L) fun C => strictN (wordS Wr L) fun Cr =>
    strictN (saltOf (invT (k / 2))) fun T =>
      strictN (mulS (mulS C (saltOf (rhoBits (k % 2)))) Cr) fun X =>
        (eqS (mulS X T) (mulS T X)).toNat

end CFSG.KC.F4Syl3

end
