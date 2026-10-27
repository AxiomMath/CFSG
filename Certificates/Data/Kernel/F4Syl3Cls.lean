module

public import Certificates.Data.Kernel.F4Syl3PhiInv

public section

namespace CFSG.KC.F4Syl3

open CFSG.LieType.Simplicity.TitsBits CFSG.KC.F4Salt CFSG.KC.Loop

@[expose] noncomputable def pinB (pS : List Nat) (W4 L4 W5 L5 : Nat) : Bool :=
  Nat.beq (sBits 0) (pS.getD 0 0) && Nat.beq (sBits 1) (pS.getD 1 0) &&
    Nat.beq (sBits 2) (pS.getD 2 0) && Nat.beq (sBits 3) (pS.getD 3 0) &&
    Nat.beq (wordS W4 L4) (saltOf (pS.getD 4 0)) && Nat.beq (wordS W5 L5) (saltOf (pS.getD 5 0))

@[expose] noncomputable def phiS (S : List Nat) (G4 G5 m : Nat) : Nat :=
  mulS (fSS S (m % 81)) (mulS (powS G4 (m / 81 % 3)) (powS G5 (m / 81 / 3 % 3)))

@[expose] noncomputable def tgtS (S : List Nat) (t : Nat) : Nat :=
  if t = 0 then S.getD 3 0 else if t = 1 then mulS (S.getD 0 0) (S.getD 1 0) else
    mulS (mulS (mulS (S.getD 0 0) (S.getD 0 0)) (mulS (S.getD 1 0) (S.getD 1 0)))
      (mulS (S.getD 2 0) (S.getD 2 0))

@[expose] noncomputable def clsRowN (pS tgt cpar clet ca cb cw cl : List Nat) (k : Nat) : Nat :=
  strictN (saltOf (pS.getD 0 0)) fun S0 => strictN (saltOf (pS.getD 1 0)) fun S1 =>
    strictN (saltOf (pS.getD 2 0)) fun S2 => strictN (saltOf (pS.getD 3 0)) fun S3 =>
      strictN (saltOf (pS.getD 4 0)) fun G4 => strictN (saltOf (pS.getD 5 0)) fun G5 =>
        strictN (phiS [S0, S1, S2, S3] G4 G5 (ca.getD k 0)) fun A =>
          if cpar.getD k 0 = 48 then
            strictN (wordS (cw.getD k 0) (cl.getD k 0)) fun C =>
              (eqS (mulS C A) (mulS (tgtS [S0, S1, S2, S3] (tgt.getD k 3)) C)).toNat
          else
            strictN (letS (clet.getD k 0)) fun L =>
              (eqS (mulS L A) (mulS (phiS [S0, S1, S2, S3] G4 G5 (cb.getD k 0)) L)).toNat

@[expose] def clsOf (cover : List (Nat × Nat)) (m : Nat) : Nat := (cover.getD m (0, 0)).2

@[expose] def ord3 (m : Nat) : Bool := m < 729 && m != 0 && pmul (pmul m m) m == 0

@[expose] def clsModelB (tgt : List Nat) (cover : List (Nat × Nat)) (cpar ca cb cdep : List Nat) :
    Bool :=
  allB 48 fun k => ord3 (ca.getD k 0) && clsOf cover (ca.getD k 0) == k &&
    (cpar.getD k 0 == 48 || (cpar.getD k 0 < 48 && ord3 (cb.getD k 0) &&
      clsOf cover (cb.getD k 0) == cpar.getD k 0 &&
      tgt.getD (cpar.getD k 0) 3 == tgt.getD k 3 &&
      cdep.getD (cpar.getD k 0) 0 < cdep.getD k 0))

end CFSG.KC.F4Syl3

end
