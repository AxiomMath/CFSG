module

public import Certificates.Data.Kernel.MergeG

public section

namespace CFSG.KC.MergeG

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch

@[expose] noncomputable def mergeTCKG (n w kG : Nat) (GS : Nat → Nat) (b x Lc S NS : Nat)
    (RI RU RV : Nat → Nat) (TP PP : Nat) (A : Nat → Nat) (ts : List Nat) : Bool :=
  bAnd(Nat.blt b n, bAnd(Nat.blt x n, bAnd(Nat.blt Lc 4096, bAnd(Nat.blt 0 S,
  bAnd(Nat.ble Lc (Nat.mul S NS),
  bAnd(allN n (fun y => Nat.beq (pgW w (A 0) y) (nIf(Nat.beq y x, b, y))),
  bAnd(allN NS (segCG n w kG GS Lc S TP PP A RI RU RV),
  bAnd(allN n (fun l => Nat.ble (pgW 12 TP l) Lc),
  bAnd(Nat.beq (mergeCnt n w GS Lc S TP PP A RI RU RV) (timedCnt n Lc TP),
    ts.all fun t => bAnd(Nat.blt t n, Nat.beq (pgW w (A NS) t) (pgW w (A NS) b)))))))))))

end CFSG.KC.MergeG

end
