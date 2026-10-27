module

public import Certificates.Data.Kernel.Misc.YamakiA0
public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KD.YamakiRep

open CFSG.KD.BfsK CFSG.KC.Loop CFSG.KD.YamakiA0
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def rstG (R : Nat → Nat) (g x s : Nat) : Nat := MULF x (R (Nat.add g s))

@[expose] noncomputable def buildAt (st : Nat → Nat → Nat) (X PA PB : Nat → Nat) (n k i : Nat) :
    Bool :=
  cond (Nat.blt (Nat.succ i) n)
    (Nat.ble (PA i) i && Nat.blt (PB i) k && Nat.beq (X (Nat.succ i)) (st (X (PA i)) (PB i))) true

@[expose] noncomputable def stepAt (st : Nat → Nat → Nat) (X PA PB C POS : Nat → Nat) (n k i : Nat) :
    Bool :=
  Nat.blt (Nat.div i k) (C i) && Nat.ble (POS i) (C i) && Nat.blt (POS i) n &&
    Nat.beq (X (POS i)) (st (X (Nat.div i k)) (Nat.mod i k)) &&
    cond (Nat.beq (POS i) (C i))
      (Nat.beq (C (Nat.succ i)) (Nat.succ (C i)) && Nat.beq (PA (Nat.pred (C i))) (Nat.div i k) &&
        Nat.beq (PB (Nat.pred (C i))) (Nat.mod i k))
      (Nat.beq (C (Nat.succ i)) (C i))

@[expose] noncomputable def sortAt (X SRT SRI : Nat → Nat) (n i : Nat) : Bool :=
  Nat.blt (SRT i) n && Nat.blt (SRI i) n && Nat.beq (SRI (SRT i)) i && Nat.beq (SRT (SRI i)) i &&
    cond (Nat.blt (Nat.succ i) n) (Nat.blt (X (SRT i)) (X (SRT (Nat.succ i)))) true

@[expose] noncomputable def rowK (R : Nat → Nat) (st : Nat → Nat → Nat) (o n k t : Nat) : Bool :=
  buildAt st (recX R o) (recF R o 0) (recF R o 1) n k t &&
    allBelow k 1 (fun s => stepAt st (recX R o) (recF R o 0) (recF R o 1) (recC R o k)
      (recPOS R o k) n k (Nat.add (Nat.mul t k) s)) &&
    sortAt (recX R o) (recF R o 2) (recF R o 3) n t

@[expose] noncomputable def chunkK (R : Nat → Nat) (st : Nat → Nat → Nat) (o n k L q : Nat) :
    Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t => cond (Nat.blt t n) (rowK R st o n k t) true

@[expose] noncomputable def headK (R : Nat → Nat) (o n k : Nat) : Bool :=
  Nat.beq (recX R o 0) ONE && Nat.beq (recC R o k 0) 1 && Nat.beq (recC R o k (Nat.mul n k)) n

@[expose] noncomputable def genWK (R : Nat → Nat) : Nat → List (List Nat) → Bool
  | _, [] => true
  | g, w :: ws => Nat.beq (R g) (wordN R w) && genWK R (Nat.succ g) ws

@[expose] noncomputable def genIK (R : Nat → Nat) : Nat → List Nat → Bool
  | _, [] => true
  | g, i :: is => Nat.beq (R g) (R i) && genIK R (Nat.succ g) is

end CFSG.KD.YamakiRep

end
