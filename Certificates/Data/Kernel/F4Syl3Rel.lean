module

public import Certificates.Data.Kernel.F4Salt
public import Certificates.Data.Kernel.F4Syl3Model

public section

namespace CFSG.KC.F4Syl3

open CFSG.LieType.Simplicity.TitsBits CFSG.KC.F4Salt CFSG.KC.Loop

@[expose] def posPS : List Nat := [1, 7, 15, 43]

@[expose] def posNS : List Nat := [6, 14, 23, 46]

@[expose] def sBits (i : Nat) : Nat :=
  mul (pack (eltBits (posPS.getD i 0))) (pack (eltBits (posNS.getD i 0)))

@[expose] noncomputable def powS (A : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) oneS (fun _ acc => mulS acc A) n

@[expose] noncomputable def fSS (S : List Nat) (a : Nat) : Nat :=
  mulS (mulS (mulS (powS (S.getD 0 0) (dg a 0)) (powS (S.getD 1 0) (dg a 1)))
    (powS (S.getD 2 0) (dg a 2))) (powS (S.getD 3 0) (dg a 3))

@[expose] noncomputable def relB (S : List Nat) (G4 G5 : Nat) : Bool :=
  allB 4 (fun i => allB 4 fun j =>
    eqS (mulS (S.getD i 0) (S.getD j 0)) (mulS (S.getD j 0) (S.getD i 0))) &&
  allB 4 (fun i => eqS (mulS (mulS (S.getD i 0) (S.getD i 0)) (S.getD i 0)) oneS) &&
  eqS (mulS (mulS G4 G4) G4) oneS && eqS (mulS (mulS G5 G5) G5) oneS &&
  eqS (mulS G4 G5) (mulS G5 G4) &&
  allB 4 (fun i => eqS (mulS G4 (S.getD i 0)) (mulS (fSS S (m4 (3 ^ i))) G4)) &&
  allB 4 (fun i => eqS (mulS G5 (S.getD i 0)) (mulS (fSS S (m5 (3 ^ i))) G5)) &&
  !eqS (fSS S 26) oneS

@[expose] noncomputable def relN (W4 L4 W5 L5 : Nat) : Nat :=
  strictN (saltOf (sBits 0)) fun S0 => strictN (saltOf (sBits 1)) fun S1 =>
    strictN (saltOf (sBits 2)) fun S2 => strictN (saltOf (sBits 3)) fun S3 =>
      strictN (wordS W4 L4) fun G4 => strictN (wordS W5 L5) fun G5 =>
        (relB [S0, S1, S2, S3] G4 G5).toNat

end CFSG.KC.F4Syl3

end
