module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.YModel.Text
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.MergeT

open CFSG.KC.Enum
open CFSG.KS (mask)
open CFSG.KC.YModel (lget)

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def mapE (f : Nat → Nat) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun a _ ih => strictL (f a) fun v => v :: ih) L

@[expose] noncomputable def relabelL (L : List Nat) (p q : Nat) : List Nat :=
  strictL (lget L q) fun lq => strictL (lget L p) fun lp =>
    mapE (fun l => nIf(Nat.beq l lq, lp, l)) L

@[expose] noncomputable def initL (n b x : Nat) : List Nat :=
  (List.range n).map fun i => nIf(Nat.beq i x, b, i)

@[expose] noncomputable def mergeStepK (n w : Nat) (GP : Nat → Nat) (kG : Nat) (st : Bool × List Nat)
    (t : Nat × Nat × Nat) : Bool × List Nat :=
  (bAnd(st.1, bAnd(Nat.blt t.1 kG, bAnd(Nat.blt t.2.1 n, bAnd(Nat.blt t.2.2 n,
      Nat.beq (lget st.2 t.2.1) (lget st.2 t.2.2))))),
    relabelL st.2 (pg w (mask w) (GP t.1) t.2.1) (pg w (mask w) (GP t.1) t.2.2))

@[expose] noncomputable def mergeTK (n w : Nat) (GP : Nat → Nat) (kG b x : Nat)
    (L : List (Nat × Nat × Nat)) (ts : List Nat) : Bool :=
  bAnd(Nat.blt b n, bAnd(Nat.blt x n,
    bAnd((L.foldl (mergeStepK n w GP kG) (true, initL n b x)).1,
      ts.all fun t => bAnd(Nat.blt t n,
        Nat.beq (lget (L.foldl (mergeStepK n w GP kG) (true, initL n b x)).2 t)
          (lget (L.foldl (mergeStepK n w GP kG) (true, initL n b x)).2 b)))))

end CFSG.KC.MergeT

end
