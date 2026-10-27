module

public import Certificates.Data.Kernel.Misc.YamakiCE

public section

namespace CFSG.KD.YamakiA6

open CFSG.KD.BfsK CFSG.KD.YamakiCE

@[expose] noncomputable def decL (P : Nat) : List Nat :=
  [P % 8, P / 8 % 8, P / 64 % 8, P / 512 % 8, P / 4096 % 8, P / 32768 % 8]

@[expose] noncomputable def compL (p q : List Nat) : List Nat :=
  [p.getD (q.getD 0 0) 0, p.getD (q.getD 1 0) 0, p.getD (q.getD 2 0) 0, p.getD (q.getD 3 0) 0,
    p.getD (q.getD 4 0) 0, p.getD (q.getD 5 0) 0]

@[expose] noncomputable def sigL (j : Nat) : List Nat :=
  cond (Nat.beq j 0) [5, 3, 1, 2, 0, 4] [5, 1, 2, 0, 4, 3]

@[expose] noncomputable def a6At (RE RP RV : Nat → Nat) (t : Nat) : Bool :=
  CFSG.KD.YamakiRepF.strictY (RP t) fun P =>
    cond (Nat.beq t 0) (decide (decL P = [0, 1, 2, 3, 4, 5]))
        (decide (decL P = compL (decL (RP (recF RE 14 0 (Nat.pred t)))) (sigL (recF RE 14 1 (Nat.pred t))))) &&
      decide (decL (RP (recPOS RE 14 2 (Nat.add (Nat.mul t 2) 0))) = compL (decL P) (sigL 0)) &&
      decide (decL (RP (recPOS RE 14 2 (Nat.add (Nat.mul t 2) 1))) = compL (decL P) (sigL 1)) &&
      (decide (decL P = [0, 1, 2, 3, 4, 5]) == memK RV 17 32 (recX RE 14 t))

@[expose] noncomputable def a6Chunk (RE RP RV : Nat → Nat) (n L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t => cond (Nat.blt t n) (a6At RE RP RV t) true

end CFSG.KD.YamakiA6

end
