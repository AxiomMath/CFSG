module

public import Certificates.Data.Kernel.Co2SmithS.Rows
public import Certificates.Data.Kernel.Co2SmithS.Replay

public section

namespace CFSG.KC.Co2SmithS

open CFSG.KC.Co2InvS

@[expose] noncomputable def cRec (CF : Nat → Nat) (k : Nat) : Nat :=
  Nat.land (Nat.shiftRight (CF (Nat.div k 64)) (Nat.mul 576 (Nat.mod k 64)))
    (Nat.sub (Nat.pow 2 576) 1)

@[expose] noncomputable def cFld (r o w : Nat) : Nat := Nat.land (Nat.shiftRight r o) (Nat.sub (Nat.pow 2 w) 1)

@[expose] noncomputable def cE (CF : Nat → Nat) (k : Nat) : Nat := cFld (cRec CF k) 0 484

@[expose] noncomputable def cT (CF : Nat → Nat) (k l : Nat) : Nat :=
  cFld (cRec CF k) (Nat.add 484 (Nat.mul 17 l)) 17

@[expose] noncomputable def cM (CF : Nat → Nat) (N k : Nat) : Nat :=
  if k < N then cFld (cRec CF k) 518 17 else N

@[expose] noncomputable def cS (CF : Nat → Nat) (k : Nat) : Nat := cFld (cRec CF k) 535 17

@[expose] noncomputable def cP (CF : Nat → Nat) (k : Nat) : Nat := cFld (cRec CF k) 552 17

@[expose] noncomputable def cL (CF : Nat → Nat) (k : Nat) : Nat := cFld (cRec CF k) 569 1

@[expose] noncomputable def conjK (A B B4 l P : Nat) : Nat :=
  if l = 0 then mulV (mulV A P) A else mulV (mulV B P) B4

@[expose] noncomputable def classRecK (CF : Nat → Nat) (A B B4 N k : Nat) : Bool :=
  decide (cT CF k 0 < N) && decide (cT CF k 1 < N) &&
    Nat.beq (cE CF (cT CF k 0)) (conjK A B B4 0 (cE CF k)) &&
    Nat.beq (cE CF (cT CF k 1)) (conjK A B B4 1 (cE CF k)) &&
    Nat.beq (cM CF N (k + 1))
      (if k < cM CF N k then rowC (cP CF) (cL CF) (cT CF) 2 k (cM CF N k) else 0) &&
    decide (cS CF k < N) &&
    (!(decide (k + 1 < N)) || decide (cE CF (cS CF k) < cE CF (cS CF (k + 1)))) &&
    (if k = 0 then Nat.beq (cE CF 0) A && Nat.beq (cP CF 0) 0 && Nat.beq (cL CF 0) 0 &&
        Nat.beq (cM CF N 0) 1
      else decide (cP CF k < k) && Nat.beq (cE CF k) (conjK A B B4 (cL CF k) (cE CF (cP CF k))))

end CFSG.KC.Co2SmithS

end
