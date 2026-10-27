module

public import Certificates.Data.Kernel.StdOdd.Chain

public section

namespace CFSG.KC.StdOdd.Chain

open CFSG.KC.StdOdd.Orbit

@[expose] noncomputable def siftK (Ls : List (List Nat)) (Ss : List (List (List Nat))) (βs : List Nat)
    (j : Nat) (T : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => List (List (List Nat)) → Nat → List Nat → Bool)
    (fun _ _ T => k T)
    (fun Ms _ ih Ss j T => List.rec (motive := fun _ => Bool) false
      (fun S Ss' _ => walkK Ms S T fun T' =>
        andB (Nat.beq (Nat.land (neqV T' (nthN βs j) (Nat.succ j)) (Nat.shiftLeft 1 j)) 0)
          (ih Ss' (Nat.succ j) T')) Ss) Ls Ss j T

@[expose] noncomputable def pickL (O e : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun i _ ih => List.cons (nthN O i) ih) e

@[expose] noncomputable def dropLast (O : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun x t ih => List.rec (motive := fun _ => List Nat) List.nil (fun _ _ _ => List.cons x ih) t) O

@[expose] noncomputable def tailL (O : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun _ t _ => t) O

@[expose] noncomputable def levSteps (N : Nat) (rs nl : List Nat) (m : Nat) : List (List (List Nat)) :=
  Nat.rec (motive := fun _ => Nat → Nat → List (List (List Nat))) (fun _ _ => List.nil)
    (fun _ ih j N => List.cons (stepsPl N 1 1 (nthN rs j) (nthN nl j))
      (ih (Nat.succ j) (Nat.shiftRight N (Nat.mul 8 (Nat.mul (nthN rs j) (nthN nl j)))))) m 0 N

@[expose] noncomputable def refOK (X A B : Nat) (O e : List Nat) (Ls : List (List Nat))
    (Sr : List (List (List Nat))) (βs : List Nat) (FP n m : Nat) : Bool :=
  andB (Nat.beq (neqMask (mapRows X (vecsPl (dropLast O))) (vecsPl (tailL O))) 0)
    (siftK (List.cons (List.cons A (List.cons B List.nil)) Ls)
      (List.rec (motive := fun _ => List (List (List Nat))) List.nil
        (fun S _ ih => List.cons (spreadS S 1 (lenN e)) ih) Sr) βs 0
      (vecsPl (pickL O e)) fun T =>
        Nat.beq (Nat.land (memMask T (splitPl FP (Nat.div (Nat.add n 7) 8) n 156) n (Nat.succ m))
          (Nat.shiftLeft 1 m)) 0)

end CFSG.KC.StdOdd.Chain

end
