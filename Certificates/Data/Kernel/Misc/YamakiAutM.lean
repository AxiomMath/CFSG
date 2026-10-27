module

public import Certificates.Data.Kernel.Misc.YamakiAut

public section

namespace CFSG.KD.YamakiAutM

open CFSG.KD.BfsK CFSG.KD.YamakiRepF
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def pair2 (p q : Nat) : Nat := Nat.add p (Nat.mul 68719476736 q)

@[expose] noncomputable def autAtT (R RT : Nat → Nat) (a0 a1 b0 b1 t : Nat) : Bool :=
  strictY (RT t) fun P => strictY (Nat.mod P 68719476736) fun p =>
    strictY (Nat.div P 68719476736) fun q =>
      Nat.beq (RT (recPOS R 14 2 (Nat.add (Nat.mul t 2) 0))) (pair2 (MULF p a0) (MULF q b0)) &&
        Nat.beq (RT (recPOS R 14 2 (Nat.add (Nat.mul t 2) 1))) (pair2 (MULF p a1) (MULF q b1)) &&
        (Nat.beq p ONE == Nat.beq t 0) && (Nat.beq q ONE == Nat.beq t 0)

@[expose] noncomputable def autChunkT (R RT : Nat → Nat) (a0 a1 b0 b1 n L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t =>
    cond (Nat.blt t n) (autAtT R RT a0 a1 b0 b1 t) true

end CFSG.KD.YamakiAutM

end
