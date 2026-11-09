module

public import Certificates.Data.Kernel.Misc.MergeT

public section

namespace CFSG.KC.MergeT

open CFSG.KC.Enum
open CFSG.KS (mask)

@[expose] noncomputable def onesP (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => Nat.add 1 (Nat.shiftLeft ih 15)) n

@[expose] noncomputable def relabelP (R P lp lq : Nat) : Nat :=
  Nat.xor P (Nat.land (Nat.xor P (Nat.mul lp R))
    (Nat.mul (Nat.div (Nat.sub (Nat.mul 16384 R)
      (Nat.land (Nat.add (Nat.xor P (Nat.mul lq R)) (Nat.mul 16383 R)) (Nat.mul 16384 R)))
      16384) 16383))

@[expose] noncomputable def initP (n b x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc (Nat.shiftLeft (nIf(Nat.beq i x, b, i)) (Nat.mul 15 i))) n

@[expose] noncomputable def mergeStepP (n w : Nat) (GP : Nat → Nat) (kG R : Nat) (st : Bool × Nat)
    (t : Nat × Nat × Nat) : Bool × Nat :=
  (bAnd(st.1, bAnd(Nat.blt t.1 kG, bAnd(Nat.blt t.2.1 n, bAnd(Nat.blt t.2.2 n,
      Nat.beq (pg 15 (mask 15) st.2 t.2.1) (pg 15 (mask 15) st.2 t.2.2))))),
    relabelP R st.2 (pg 15 (mask 15) st.2 (pg w (mask w) (GP t.1) t.2.1))
      (pg 15 (mask 15) st.2 (pg w (mask w) (GP t.1) t.2.2)))

@[expose] noncomputable def mergeTP (n w : Nat) (GP : Nat → Nat) (kG b x : Nat)
    (L : List (Nat × Nat × Nat)) (ts : List Nat) : Bool :=
  bAnd(Nat.blt b n, bAnd(Nat.blt x n,
    bAnd((L.foldl (mergeStepP n w GP kG (onesP n)) (true, initP n b x)).1,
      ts.all fun t => bAnd(Nat.blt t n,
        Nat.beq (pg 15 (mask 15) (L.foldl (mergeStepP n w GP kG (onesP n)) (true, initP n b x)).2 t)
          (pg 15 (mask 15) (L.foldl (mergeStepP n w GP kG (onesP n)) (true, initP n b x)).2 b)))))

end CFSG.KC.MergeT

end
