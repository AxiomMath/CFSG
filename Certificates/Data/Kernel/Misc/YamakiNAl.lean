module

public import Certificates.Data.Kernel.Misc.YamakiNA

public section

namespace CFSG.KD.YamakiNA

open CFSG.KD.BfsK
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def cAlChunk (R : Nat → Nat) (o n : Nat) (RX : Nat → Nat) (oX nX : Nat)
    (P : Nat → Nat) (L q : Nat) : Bool :=
  CFSG.KD.YamakiRepF.strictY (R 5) fun a =>
    CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t => cond (Nat.blt t n)
      (CFSG.KD.YamakiRepF.strictY (recX R o t) fun x =>
        !(Nat.beq (MULF x a) (MULF a x)) || (Nat.blt (P t) nX && Nat.beq (recX RX oX (P t)) x))
      true

end CFSG.KD.YamakiNA

end
