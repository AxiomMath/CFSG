module

public import Certificates.Data.Kernel.Misc.OmegaSixC

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.BfsK CFSG.KD.YamakiRepF CFSG.KC.Loop
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def rowB3 (R : Nat → Nat) (st : Nat → Nat → Nat) (o n t r r' : Nat) :
    Bool :=
  strictY (Nat.land r M64) fun x => strictY (fld r 0) fun pa => strictY (fld r 1) fun pb =>
  strictY (fld r 4) fun c0 => strictY (fld r 5) fun c1 => strictY (fld r 6) fun c2 =>
  strictY (fld r' 4) fun c3 => strictY (fld r 2) fun srt => strictY (fld r 3) fun sri =>
    cond (Nat.blt (Nat.succ t) n)
      (Nat.ble pa t && Nat.blt pb 3 && Nat.beq (Nat.land r' M64) (st (recX R o pa) pb)) true &&
    stepF R st o n t 0 x c0 (fld r 7) c1 &&
    stepF R st o n t 1 x c1 (fld r 8) c2 &&
    stepF R st o n t 2 x c2 (fld r 9) c3 &&
    (Nat.blt srt n && Nat.blt sri n && Nat.beq (recF R o 3 srt) t && Nat.beq (recF R o 2 sri) t &&
      cond (Nat.blt (Nat.succ t) n) (Nat.blt (recX R o srt) (recX R o (fld r' 2))) true)

@[expose] noncomputable def rowF3 (R : Nat → Nat) (st : Nat → Nat → Nat) (o n t : Nat) : Bool :=
  strictY (R (Nat.add o t)) fun r => strictY (R (Nat.add o (Nat.succ t))) fun r' =>
    rowB3 R st o n t r r'

@[expose] noncomputable def chunkF3 (R : Nat → Nat) (st : Nat → Nat → Nat) (o n L q : Nat) :
    Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t => cond (Nat.blt t n) (rowF3 R st o n t) true

@[expose] noncomputable def anyK (k : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(f i, true, ih)) k

@[expose] noncomputable def bitK (X p : Nat) : Nat := Nat.land (Nat.shiftRight X p) 1

@[expose] noncomputable def colK (X c : Nat) : Nat :=
  Nat.add (bitK X c) (Nat.add (Nat.mul 2 (bitK X (Nat.add 6 c)))
    (Nat.add (Nat.mul 4 (bitK X (Nat.add 12 c))) (Nat.add (Nat.mul 8 (bitK X (Nat.add 18 c)))
      (Nat.add (Nat.mul 16 (bitK X (Nat.add 24 c))) (Nat.mul 32 (bitK X (Nat.add 30 c)))))))

@[expose] noncomputable def subK (X c : Nat) : Nat := Nat.xor (colK X c) (Nat.shiftLeft 1 c)

@[expose] noncomputable def twoNZK (X : Nat) : Bool :=
  anyK 6 fun c => strictY (subK X c) fun a => bIf(Nat.beq a 0, false,
    anyK 6 fun d => strictY (subK X d) fun b => bIf(Nat.beq b 0, false, bIf(Nat.beq a b, false,
      true)))

@[expose] noncomputable def reflAt (RR : Nat → Nat) (nR X : Nat) : Bool :=
  bIf(memK RR 5 nR X, true, bIf(Nat.beq X ONE, true, twoNZK X))

@[expose] noncomputable def reflChunk (R : Nat → Nat) (o n : Nat) (RR : Nat → Nat) (nR L q : Nat) :
    Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t =>
    bIf(Nat.blt t n, strictY (recX R o t) (reflAt RR nR), true)

@[expose] noncomputable def a6cAt (w₁ w₂ r X : Nat) : Bool :=
  bIf(Nat.beq (MULF X w₁) (MULF w₁ X),
    bIf(Nat.beq (MULF X w₂) (MULF w₂ X), bIf(Nat.beq X ONE, true, Nat.beq X r), true), true)

@[expose] noncomputable def a6cChunk (R : Nat → Nat) (o n w₁ w₂ r L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t =>
    bIf(Nat.blt t n, strictY (recX R o t) (a6cAt w₁ w₂ r), true)

@[expose] noncomputable def commK (x y : Nat) : Nat := MULF (MULF (MULF x y) x) y

end CFSG.KD.OmegaSix

end
