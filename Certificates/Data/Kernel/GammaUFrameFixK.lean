module

public import Certificates.Data.Kernel.IdxFourSiftK
public import Certificates.Data.Kernel.GammaUNormK
public import Certificates.Data.Kernel.GammaUSigmaK
public import CFSG.GF2Type.Smith1979.GammaU.SigmaInputs

public section

namespace CFSG.KC.GUX

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUV CFSG.KC.GUS
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

@[expose] noncomputable def allL (f : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => f a && ih) l

@[expose] noncomputable def fixK (PG : List Nat) : Bool :=
  allBelow 4096 fun n =>
    Nat.beq n 0 || Nat.beq n 3072 || !(allL (fun P => Nat.beq (ap12 P n) n) PG)

@[expose] def perpB : List ℕ := [1, 2, 4, 8, 48, 64, 128, 256, 512, 1024, 2048]

@[expose] noncomputable def rowsG (i : ℕ) : Bool :=
  (ResPair.compGens i).all fun r => rowsOK r.toList

@[expose] noncomputable def rowsC (i : ℕ) : Bool := (compOf i).all fun r => rowsOK r.toList

@[expose] noncomputable def fix (i : ℕ) : Bool := fixK ((ResPair.compGens i).map packR)

@[expose] def fixA (i : ℕ) : Bool := (compOf i).all fun r => appN r a0 == a0

@[expose] def comm (i : ℕ) : Bool :=
  (compOf i).all fun r => perpB.all fun c => (spanList d0).contains (appN r c ^^^ c)

@[expose] def wit (i : ℕ) : Bool :=
  (compOf i).length == 32 &&
    !f0b 65 a0 && !f0b 1 a0 && !f0b 385 a0 && !f0b 320 a0 && !f0b 192 a0 &&
    (appN ((compOf i).getD 16 idR) 65 ^^^ 65) == 961 &&
    (appN ((compOf i).getD 8 idR) 1 ^^^ 1) == 48 &&
    (appN ((compOf i).getD 16 idR) 385 ^^^ 385) == 9 &&
    (appN ((compOf i).getD 16 idR) 320 ^^^ 320) == 5 &&
    (appN ((compOf i).getD 16 idR) 192 ^^^ 192) == 3

@[expose] noncomputable def n2 (i : ℕ) : Bool :=
  (ResPair.n2Gens i).all fun r => rowsOK r.toList &&
    guOK (packR SigmaP.thetaRows) (packR r) && (unitaryN r || antiN r)

end CFSG.KC.GUX

end
