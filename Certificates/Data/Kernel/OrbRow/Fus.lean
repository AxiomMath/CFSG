module

public import Certificates.Data.Kernel.OrbRow.Cent

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum CFSG.KC.PGrp

@[expose] noncomputable def dgtWord (k : Nat) : List Nat :=
  List.replicate (k % 3) 0 ++ (List.replicate (k / 3 % 3) 1 ++
    (List.replicate (k / 9 % 3) 2 ++ List.replicate (k / 27 % 3) 3))

@[expose] noncomputable def fusK (n w m : Nat) (D H : List Nat) (XA XB : Nat) (FI FC FE : List Nat)
    (k : Nat) : Bool :=
  strictB (getS FI k) fun j => strictB (getS FC k) fun c => strictB (getS FE k) fun e =>
  strictB (getS H j) fun h => strictB (CFSG.KS.pinvS n w m h) fun hi =>
    bAnd(Nat.blt j (lenS H), bAnd(Nat.blt c (nat_lit 2),
    bAnd(Nat.ble (nat_lit 1) e, bAnd(Nat.ble e (nat_lit 2),
    bAnd(permOK n w m (Nat.mul n w) h hi,
      Nat.beq (pcomp n w m h (pcomp n w m (posWordK n w (getS D) (dgtWord k)) hi))
        (posWordK n w (fun _ => nIf(Nat.beq c (nat_lit 0), XA, XB)) (List.replicate e 0)))))))

end CFSG.KC.OrbRow

end
