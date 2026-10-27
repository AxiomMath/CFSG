module

public import Certificates.Data.Kernel.L34Cov.T1

public section

namespace CFSG.KC.L34Cov

open CFSG.KC CFSG.KC.Loop CFSG.KC.L34W

@[expose] noncomputable def corrC (e vA vB eA eB : Nat) : Nat :=
  Nat.add (Nat.add
    (Nat.mod (Nat.add (Nat.add (Nat.div (Nat.mod e 48) 12) (Nat.mul (Nat.sub 12 eA) (Nat.mod vA 4)))
      (Nat.mul (Nat.sub 12 eB) (Nat.mod vB 4))) 4)
    (Nat.mul 4 (Nat.mod (Nat.add (Nat.add (Nat.div (Nat.mod e 12) 3)
      (Nat.mul (Nat.sub 12 eA) (Nat.mod (Nat.div vA 4) 4)))
      (Nat.mul (Nat.sub 12 eB) (Nat.mod (Nat.div vB 4) 4))) 4)))
    (Nat.mul 16 (Nat.mod (Nat.add (Nat.add (Nat.mod e 3) (Nat.mul (Nat.sub 12 eA) (Nat.div vA 16)))
      (Nat.mul (Nat.sub 12 eB) (Nat.div vB 16))) 3))

@[expose] noncomputable def alGenOK (V : Nat) (TA TB : Nat → Nat) (C : List (List Nat))
    (A : Nat → Nat) (uA uB : List Nat) (vA vB i k : Nat) : Bool :=
  bindB (ent A i k) fun e =>
    zvOK V TA TB (substC [uA, uB] (C.getD k []) ++ invW (C.getD (Nat.div e 48) []))
      (corrC e vA vB (eN 0 (C.getD k [])) (eN 1 (C.getD k [])))

@[expose] noncomputable def alGensOK (V : Nat) (TA TB : Nat → Nat) (F C : List (List Nat))
    (A : Nat → Nat) (uA uB : List Nat) (i : Nat) : Bool :=
  bindB (zvC V TA TB (invW uA ++ substC [uA, uB] (F.getD 0 []))) fun vA =>
  bindB (zvC V TA TB (invW uB ++ substC [uA, uB] (F.getD 1 []))) fun vB =>
    andB (zvOK V TA TB (invW uA ++ substC [uA, uB] (F.getD 0 [])) vA)
    (andB (zvOK V TA TB (invW uB ++ substC [uA, uB] (F.getD 1 [])) vB)
    (andB (alGenOK V TA TB C A uA uB vA vB i 1) (andB (alGenOK V TA TB C A uA uB vA vB i 2)
    (andB (alGenOK V TA TB C A uA uB vA vB i 16) (alGenOK V TA TB C A uA uB vA vB i 20)))))

end CFSG.KC.L34Cov

end
