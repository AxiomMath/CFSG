module

public import Certificates.Data.Kernel.Misc.YamakiCE
public import Certificates.Data.Sp62RecCR1NA

public section

namespace CFSG.KD.YamakiNA

open CFSG.KD.BfsK CFSG.KD.YamakiA0 CFSG.KD.YamakiCE CFSG.ClassicalInvolution.Sp62Rec
  CFSG.ClassicalInvolution.Solomon73.Yamaki
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def comm6 (R : Nat → Nat) (x : Nat) : Bool :=
  (List.range 6).all fun j => Nat.beq (MULF x (R (Nat.add j 3))) (MULF (R (Nat.add j 3)) x)

@[expose] noncomputable def cA0Chunk (R : Nat → Nat) (o n : Nat) (RA : Nat → Nat) (L q : Nat) :
    Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t => cond (Nat.blt t n)
    (CFSG.KD.YamakiRepF.strictY (recX R o t) fun x => !(comm6 R x) || memK RA 12 64 x) true

@[expose] noncomputable def normA0K (R : Nat → Nat) : Bool :=
  idxN0.all fun s => (List.range 6).all fun j =>
    memK R 12 64 (MULF (MULF (R s) (R (Nat.add j 3))) (R s))

@[expose] noncomputable def sevenK (R : Nat → Nat) : Bool :=
  Nat.beq (wordN R (List.replicate 7 sevenWord).flatten) ONE && !(Nat.beq (wordN R sevenWord) ONE) &&
    (List.range 64).all fun t => !(Nat.beq (MULF (recX R 12 t) (wordN R sevenWord))
      (MULF (wordN R sevenWord) (recX R 12 t))) || Nat.beq (recX R 12 t) ONE

@[expose] noncomputable def alphaClassK (R : Nat → Nat) : Bool :=
  decide (alphaClassWords.map fun c => wordN R (conjWord c [5])).Nodup

end CFSG.KD.YamakiNA

end
