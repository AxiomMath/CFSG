module

public import Certificates.Data.Kernel.Misc.YamakiCE

public section

namespace CFSG.KD.YamakiE64

open CFSG.KD.BfsK CFSG.KD.YamakiCE
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def candsN (R : Nat → Nat) (o n b : Nat) : List Nat :=
  ((List.range n).map (recX R o)).filter fun x =>
    Nat.beq (MULF x x) ONE && Nat.beq (MULF x b) (MULF b x)

@[expose] noncomputable def coreLen (T : List Nat) : Nat :=
  (T.filter fun x => decide (64 ≤ (T.filter fun y => Nat.beq (MULF x y) (MULF y x)).length)).length

@[expose] noncomputable def e64At (R : Nat → Nat) (o : Nat) (RA : Nat → Nat) (oA t : Nat) : Bool :=
  CFSG.KD.YamakiRepF.strictY (recX R o t) fun b =>
    memK RA oA 64 b || !(Nat.beq (MULF b b) ONE) || decide (coreLen (candsN R o 512 b) < 64)

@[expose] noncomputable def e64Chunk (R : Nat → Nat) (o : Nat) (RA : Nat → Nat) (oA L q : Nat) :
    Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t => cond (Nat.blt t 512) (e64At R o RA oA t) true

end CFSG.KD.YamakiE64

end
