module

public import Certificates.Data.Kernel.Misc.YamakiA6

public section

namespace CFSG.KD.YamakiA6

open CFSG.KD.BfsK CFSG.KD.YamakiCE

@[expose] noncomputable def dg (P k : Nat) : Nat := Nat.mod (Nat.div P k) 8

@[expose] noncomputable def cS0 (Q : Nat) : Nat :=
  Nat.add (dg Q 32768) (Nat.add (Nat.mul 8 (dg Q 512)) (Nat.add (Nat.mul 64 (dg Q 8))
    (Nat.add (Nat.mul 512 (dg Q 64)) (Nat.add (Nat.mul 4096 (dg Q 1)) (Nat.mul 32768 (dg Q 4096))))))

@[expose] noncomputable def cS1 (Q : Nat) : Nat :=
  Nat.add (dg Q 32768) (Nat.add (Nat.mul 8 (dg Q 8)) (Nat.add (Nat.mul 64 (dg Q 64))
    (Nat.add (Nat.mul 512 (dg Q 1)) (Nat.add (Nat.mul 4096 (dg Q 4096)) (Nat.mul 32768 (dg Q 512))))))

@[expose] noncomputable def cS (j Q : Nat) : Nat := cond (Nat.beq j 0) (cS0 Q) (cS1 Q)

@[expose] noncomputable def a6AtN (RE RP RV : Nat → Nat) (t : Nat) : Bool :=
  CFSG.KD.YamakiRepF.strictY (RP t) fun P =>
    Nat.blt P 262144 &&
      cond (Nat.beq t 0) (Nat.beq P 181896)
        (Nat.beq P (cS (recF RE 14 1 (Nat.pred t)) (RP (recF RE 14 0 (Nat.pred t))))) &&
      Nat.beq (RP (recPOS RE 14 2 (Nat.add (Nat.mul t 2) 0))) (cS0 P) &&
      Nat.beq (RP (recPOS RE 14 2 (Nat.add (Nat.mul t 2) 1))) (cS1 P) &&
      cond (Nat.beq P 181896) (memK RV 17 32 (recX RE 14 t)) true

@[expose] noncomputable def a6ChunkN (RE RP RV : Nat → Nat) (n L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t => cond (Nat.blt t n) (a6AtN RE RP RV t) true

@[expose] noncomputable def a6VK (RE RP RV PV : Nat → Nat) : Bool :=
  (List.range 32).all fun v =>
    Nat.blt (PV v) 11520 && Nat.beq (recX RE 14 (PV v)) (recX RV 17 v) && Nat.beq (RP (PV v)) 181896

end CFSG.KD.YamakiA6

end
