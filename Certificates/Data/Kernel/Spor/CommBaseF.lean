module

public import Certificates.Data.Kernel.Spor.CommBase

public section

namespace CFSG.KC.CommBase

open CFSG.KC.Enum

abbrev Fix3Rec : Type := Nat × List (List Nat) × Nat × Nat

@[expose] noncomputable def fix3OK (n w m : Nat) (L : Nat → Nat) (nL : Nat) (r : Fix3Rec) : Bool :=
  bAnd(Nat.blt r.1 n, bAnd(Nat.blt r.2.2.1 n, bAnd(Nat.blt r.2.2.2 n,
  bAnd(allL (lettersOK nL) r.2.1,
  bAnd(fixAll w m L r.2.1 r.1,
  allN n (fun y => bIf(fixAll w m L r.2.1 y,
    bIf(Nat.beq y r.1, true, bIf(Nat.beq y r.2.2.1, true, Nat.beq y r.2.2.2)), true)))))))

@[expose] def fix3Root (r : Fix3Rec) : BaseRec := (r.1, [], [], [], r.1)

@[expose] noncomputable def commBaseF (n w m : Nat) (L : Nat → Nat) (nL : Nat) (B : List BaseRec)
    (B3 : List Fix3Rec) (PF ZF DF : Nat) : Bool :=
  bAnd(allL (baseOK n w m L nL) B, bAnd(allL (fix3OK n w m L nL) B3,
    forestOK n w m L nL (B ++ B3.map fix3Root) PF ZF DF))

end CFSG.KC.CommBase

end
