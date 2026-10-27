module

public import Certificates.Data.Kernel.Spor.F3Lane
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KS.F3152

open CFSG.F3.Native CFSG.KS.F3L

@[expose] noncomputable def dgK : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 78) i))) (nat_lit 77)

@[expose] noncomputable def upK : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (mk (Nat.sub (nat_lit 76) i))
      (Nat.succ (Nat.mul (nat_lit 78) i)))) (nat_lit 77)

@[expose] noncomputable def trU (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight x t)
      (Nat.land dgK (mk (Nat.mul (nat_lit 78) (Nat.sub (nat_lit 77) t))))) (Nat.mul (nat_lit 77) t)))
    (nat_lit 77)

@[expose] noncomputable def upperOf (S : V) : V :=
  ⟨Nat.lor (Nat.land S.p upK) (Nat.land S.m dgK), Nat.lor (Nat.land S.m upK) (Nat.land S.p dgK)⟩

@[expose] noncomputable def symOf (U : V) : V := U.add ⟨trU U.p, trU U.m⟩

@[expose] noncomputable def offK (i : Nat) : Nat :=
  Nat.sub (Nat.mul (nat_lit 77) i) (Nat.div (Nat.mul i (Nat.sub i (nat_lit 1))) (nat_lit 2))

@[expose] noncomputable def plOf (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 78) i))
      (mk (Nat.sub (nat_lit 77) i))) (offK i))) (nat_lit 77)

@[expose] noncomputable def tri4 (n : Nat) : Nat :=
  Nat.add (Nat.land n (nat_lit 1)) (Nat.add
    (Nat.mul (nat_lit 3) (Nat.land (Nat.shiftRight n (nat_lit 1)) (nat_lit 1))) (Nat.add
    (Nat.mul (nat_lit 9) (Nat.land (Nat.shiftRight n (nat_lit 2)) (nat_lit 1)))
    (Nat.mul (nat_lit 27) (Nat.land (Nat.shiftRight n (nat_lit 3)) (nat_lit 1)))))

@[expose] noncomputable def bytesK (n : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun N P M => bAnd(Nat.beq N (nat_lit 10), bAnd(Nat.beq P (nat_lit 0), Nat.beq M (nat_lit 0))))
    (fun _ ih N P M => bAnd(Nat.beq (Nat.land N (nat_lit 255)) (Nat.add (nat_lit 40)
        (Nat.add (tri4 (Nat.land P (nat_lit 15))) (Nat.mul (nat_lit 2) (tri4 (Nat.land M (nat_lit 15)))))),
      ih (Nat.shiftRight N (nat_lit 8)) (Nat.shiftRight P (nat_lit 4)) (Nat.shiftRight M (nat_lit 4))))
    n

@[expose] noncomputable def eqV (X Y : V) : Bool := bAnd(Nat.beq X.p Y.p, Nat.beq X.m Y.m)

@[expose] noncomputable def lineOK (S : V) (N : Nat) : Bool :=
  bAnd(Nat.beq (Nat.land S.p S.m) (nat_lit 0), bAnd(eqV S (symOf (upperOf S)),
    bytesK (nat_lit 751) N (plOf (upperOf S).p) (plOf (upperOf S).m)))

@[expose] noncomputable def linesK (S : Nat → V) (n : Nat) : List (Nat × Nat) → Nat → Bool :=
  Nat.rec (motive := fun _ => List (Nat × Nat) → Nat → Bool) (fun _ _ => true)
    (fun _ ih L r => List.rec (motive := fun _ => Bool) false
      (fun p t _ => bAnd(Nat.beq p.2 (nat_lit 752), bAnd(lineOK (S r) p.1, ih t (Nat.succ r)))) L)
    n

@[expose] noncomputable def dropK {α : Type} (n : Nat) (L : List α) : List α :=
  Nat.rec (motive := fun _ => List α) L
    (fun _ acc => List.rec (motive := fun _ => List α) List.nil (fun _ t _ => t) acc) n

@[expose] noncomputable def nilK {α : Type} (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L

@[expose] noncomputable def spK : Nat := spreadE (nat_lit 77) (nat_lit 77)

@[expose] noncomputable def mulK (X Y : V) : V := mulLane (nat_lit 77) spK X Y

@[expose] noncomputable def pullK (At A : V) (G : Nat) (S : Nat → V) (n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih r => strictT (Nat.land (Nat.shiftRight G (Nat.mul (nat_lit 12) r)) (nat_lit 4095))
      fun x => bAnd(Nat.blt x (nat_lit 3510), bAnd(eqV (mulK At (mulK (S x) A)) (S r), ih (Nat.succ r))))
    n

@[expose] noncomputable def mergeK : Nat → List Nat → List Nat → List Nat
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, x :: a, [] => x :: a
  | n + 1, x :: a, y :: b =>
    Bool.rec (motive := fun _ => List Nat) (y :: mergeK n (x :: a) b) (x :: mergeK n a (y :: b))
      (Nat.blt x y)

@[expose] noncomputable def pairK (f : Nat) : List (List Nat) → List (List Nat)
  | a :: b :: l => mergeK f a b :: pairK f l
  | l => l

@[expose] noncomputable def passK (f : Nat) : Nat → List (List Nat) → List (List Nat)
  | 0, l => l
  | n + 1, l => passK f n (pairK f l)

@[expose] noncomputable def msortK (ks : List Nat) : List Nat :=
  (passK (nat_lit 8192) (nat_lit 12) (ks.map fun k => [k])).flatten

@[expose] noncomputable def sortedK : List Nat → Bool
  | x :: y :: l => bAnd(Nat.blt x y, sortedK (y :: l))
  | _ => true

end CFSG.KS.F3152

end
