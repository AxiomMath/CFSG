module

public import Certificates.Data.Kernel.F4Syl3PhiInv

public section

namespace CFSG.KC.F4Inv

open CFSG.LieType.Simplicity.TitsBits CFSG.KC.F4Salt CFSG.KC.Loop CFSG.KC.F4Syl3

@[expose] noncomputable def commN (X c : Nat) : Nat :=
  strictN (saltOf X) fun S => strictN (letS c) fun L => (eqS (mulS L S) (mulS S L)).toNat

@[expose] def longPos : List Nat := [0, 1, 5, 7, 13, 21, 15, 22, 30, 35, 39, 43]

@[expose] noncomputable def longN (W L a : Nat) : Nat :=
  strictN (wordS W L) fun C =>
    (eqS (mulS C (saltOf (invT 0))) (mulS (saltOf (pack (eltBits a))) C)).toNat

end CFSG.KC.F4Inv

end
