module

public import Certificates.Data.Kernel.Misc.YamakiRep

public section

namespace CFSG.KD.YamakiRepF

open CFSG.KD.BfsK

@[expose] noncomputable def strictY (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def fld (r f : Nat) : Nat :=
  Nat.land (Nat.shiftRight r (Nat.add 64 (Nat.mul 16 f))) 65535

@[expose] noncomputable def stepF (R : Nat → Nat) (st : Nat → Nat → Nat) (o n t s x c p c' : Nat) :
    Bool :=
  Nat.blt t c && Nat.ble p c && Nat.blt p n && Nat.beq (recX R o p) (st x s) &&
    cond (Nat.beq p c)
      (Nat.beq c' (Nat.succ c) && Nat.beq (recF R o 0 (Nat.pred c)) t &&
        Nat.beq (recF R o 1 (Nat.pred c)) s)
      (Nat.beq c' c)

@[expose] noncomputable def rowB (R : Nat → Nat) (st : Nat → Nat → Nat) (o n t r r' : Nat) : Bool :=
  strictY (Nat.land r M64) fun x => strictY (fld r 0) fun pa => strictY (fld r 1) fun pb =>
  strictY (fld r 4) fun c0 => strictY (fld r 5) fun c1 => strictY (fld r' 4) fun c2 =>
  strictY (fld r 2) fun srt => strictY (fld r 3) fun sri =>
    cond (Nat.blt (Nat.succ t) n)
      (Nat.ble pa t && Nat.blt pb 2 && Nat.beq (Nat.land r' M64) (st (recX R o pa) pb)) true &&
    stepF R st o n t 0 x c0 (fld r 6) c1 &&
    stepF R st o n t 1 x c1 (fld r 7) c2 &&
    (Nat.blt srt n && Nat.blt sri n && Nat.beq (recF R o 3 srt) t && Nat.beq (recF R o 2 sri) t &&
      cond (Nat.blt (Nat.succ t) n) (Nat.blt (recX R o srt) (recX R o (fld r' 2))) true)

@[expose] noncomputable def rowF (R : Nat → Nat) (st : Nat → Nat → Nat) (o n t : Nat) : Bool :=
  strictY (R (Nat.add o t)) fun r => strictY (R (Nat.add o (Nat.succ t))) fun r' =>
    rowB R st o n t r r'

@[expose] noncomputable def chunkF (R : Nat → Nat) (st : Nat → Nat → Nat) (o n L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t => cond (Nat.blt t n) (rowF R st o n t) true

end CFSG.KD.YamakiRepF

end
