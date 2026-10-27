module

public import Certificates.Data.Kernel.Sp43KList

public noncomputable section

namespace CFSG.KC.Sp43K

@[expose] def conjT (n n' c : Nat) : Nat := mulT (mulT n c) n'

@[expose] def tOne (a b a' b' N T i : Nat) (q : Nat × Nat) : Bool :=
  let c := fldT T i
  okT c && (i + 1 == N || decide (c < fldT T (i + 1))) &&
    decide (q.1 < N) && fldT T q.1 == conjT a a' c && decide (q.2 < N) && fldT T q.2 == conjT b b' c

@[expose] def tGo (a b a' b' N T e : Nat) (R : List (Nat × Nat)) : Nat → Bool :=
  List.rec (fun i => i == e) (fun q _ ih i => Nat.blt i N && tOne a b a' b' N T i q && ih (i + 1)) R

@[expose] def inGo (P N T : Nat) (R : List Nat) : Nat → Bool :=
  List.rec (fun _ => true)
    (fun x _ ih i => (fldT P i == oneT || decide (x < N) && fldT T x == fldT P i) && ih (i + 1)) R

@[expose] def wordGo (a b : Nat) (w : List Nat) : Nat → Nat :=
  List.rec (fun acc => acc) (fun l _ ih acc => ih (mulT acc (genT a b l))) w

@[expose] def wordT (a b : Nat) (w : List Nat) : Nat := wordGo a b w oneT

@[expose] def oOne (n₁ n₁' n₂ n₂' k M r X N T D t : Nat) (q : Nat × Nat) : Bool :=
  let c := fldT T t
  let d := fldT D t
  (d == 0 && decide (q.1 < k) && fldT M q.1 == c) ||
    (d == 1 && decide (q.1 < r) && fldT X q.1 == c) ||
    (decide (2 ≤ d) && decide (q.1 < N) && decide (1 ≤ fldT D q.1) && decide (fldT D q.1 < d) &&
      c == (if q.2 == 0 then conjT n₁ n₁' (fldT T q.1) else conjT n₂ n₂' (fldT T q.1)))

@[expose] def oGo (n₁ n₁' n₂ n₂' k M r X N T D e : Nat) (R : List (Nat × Nat)) : Nat → Bool :=
  List.rec (fun t => t == e)
    (fun q _ ih t => Nat.blt t N && oOne n₁ n₁' n₂ n₂' k M r X N T D t q && ih (t + 1)) R

end CFSG.KC.Sp43K

end
