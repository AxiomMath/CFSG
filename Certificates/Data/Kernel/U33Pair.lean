module

public section

namespace CFSG.KC.U33Pair

@[expose] def u33T : Nat :=
  3696517080814607152696707294816937829307851364410153474058649046537449827127300363480804220535840462675046221863987508469315630113211118466872634000952931051361843600174435529456963125118574597991820138653118094

@[expose] def u33PtK (k : Nat) (x : Fin 28) : Fin 28 :=
  Fin.ofNat 28 (Nat.land (Nat.shiftRight u33T (5 * (28 * k + x.val))) 31)

@[expose] def u33StepK (d : Nat) (pq : Fin 28 × Fin 28) : Fin 28 × Fin 28 :=
  if d = 0 then pq else (u33PtK (d - 1) pq.1, u33PtK (d - 1) pq.2)

@[expose] noncomputable def u33EvalK (n : Nat) : Nat → Fin 28 × Fin 28 → Fin 28 × Fin 28 :=
  Nat.rec (motive := fun _ => Nat → Fin 28 × Fin 28 → Fin 28 × Fin 28) (fun _ pq => pq)
    (fun _ ih c pq => ih (c / 6) (u33StepK (c % 6) pq)) n

@[expose] noncomputable def u33OkK (i c : Nat) : Bool :=
  Nat.beq (i / 28) (i % 28) ||
    decide (u33EvalK 9 c (0, 1) = (Fin.ofNat 28 (i / 28), Fin.ofNat 28 (i % 28)))

@[expose] noncomputable def u33PairsK (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih i => u33OkK i c && ih (i + 1)) L

end CFSG.KC.U33Pair
