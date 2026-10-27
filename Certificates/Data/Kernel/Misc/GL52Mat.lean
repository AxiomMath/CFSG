module

public import CFSG.Certificates.Kernel.Orders.Mat
public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.Misc.GLM

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def bitK (x i : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight x i) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def rowK (c i : Nat) : Nat :=
  Nat.land (Nat.shiftRight c (Nat.mul (nat_lit 5) i)) (nat_lit 31)

@[expose] noncomputable def selK (r b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (rowK b k)) (bitK r k))
    (nat_lit 5)

@[expose] noncomputable def mmulK (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (selK (rowK a i) b) (Nat.mul (nat_lit 5) i)))
    (nat_lit 5)

@[expose] noncomputable def idK : Nat := nat_lit 17043521

@[expose] noncomputable def zerosK (W : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil (fun _ acc => List.cons (nat_lit 0) acc) W

@[expose] noncomputable def insK (o : Nat) : List Nat → Nat → Nat → List Nat :=
  List.rec (motive := fun _ => Nat → Nat → List Nat) (fun _ _ => List.nil)
    (fun s rest ih t r =>
      Bool.rec (motive := fun _ => List Nat) (List.cons s (ih (Nat.sub t 1) r))
        (Bool.rec (motive := fun _ => List Nat) (List.cons s (ih (Nat.sub t 1) (Nat.xor r s)))
          (List.cons r rest) (Nat.beq s (nat_lit 0)))
        (bitK r (Nat.add t o)))

@[expose] noncomputable def redK (o : Nat) : List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ r => r)
    (fun s _ ih t r =>
      ih (Nat.sub t 1)
        (Bool.rec (motive := fun _ => Nat) r
          (Bool.rec (motive := fun _ => Nat) (Nat.xor r s) r (Nat.beq s (nat_lit 0)))
          (bitK r (Nat.add t o))))

@[expose] noncomputable def cntNZ : List Nat → Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun s _ ih => Nat.add ih (Bool.rec (motive := fun _ => Nat) (nat_lit 1) (nat_lit 0)
      (Nat.beq s (nat_lit 0))))

@[expose] noncomputable def rankK (c : Nat) : Nat :=
  cntNZ (Nat.rec (motive := fun _ => List Nat) (zerosK (nat_lit 5))
    (fun i acc => insK (nat_lit 0) acc (nat_lit 4) (rowK c i)) (nat_lit 5))

@[expose] noncomputable def imgK (ps : List (Nat × Nat)) (idx : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun p _ ih sh => Prod.rec (motive := fun _ => Nat)
      (fun A B => Nat.lor (Nat.shiftLeft (Nat.xor (mmulK (Nat.shiftLeft (nat_lit 1) idx) A)
        (mmulK B (Nat.shiftLeft (nat_lit 1) idx))) sh) (ih (Nat.add sh (nat_lit 25)))) p)
    ps (nat_lit 0)

@[expose] noncomputable def elimK (ps : List (Nat × Nat)) (W : Nat) (k : Nat) : List Nat × List Nat :=
  Nat.rec (motive := fun _ => List Nat × List Nat) (Prod.mk (zerosK W) List.nil)
    (fun idx st => Prod.rec (motive := fun _ => List Nat × List Nat)
      (fun slots ker =>
        letB (Nat.lor (Nat.shiftLeft (imgK ps idx) (nat_lit 25)) (Nat.shiftLeft (nat_lit 1) idx))
          fun r0 => letB (redK (nat_lit 25) slots (Nat.sub W 1) r0) fun r =>
            Bool.rec (motive := fun _ => List Nat × List Nat)
              (Prod.mk (insK (nat_lit 25) slots (Nat.sub W 1) r) ker)
              (Prod.mk slots (List.cons r ker))
              (Nat.blt r (nat_lit 33554432))) st) k
where
  letB (y : Nat) (k : Nat → List Nat × List Nat) : List Nat × List Nat :=
    Nat.rec (motive := fun _ => List Nat × List Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def xsel (L : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih j => Nat.xor (Bool.rec (motive := fun _ => Nat) (nat_lit 0) x (bitK m j))
      (ih (Nat.succ j))) L (nat_lit 0)

@[expose] noncomputable def unitCntR (L : List Nat) (lo cnt : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun d acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (Nat.beq (rankK (xsel L (Nat.add lo d))) (nat_lit 5))))
    cnt

@[expose] noncomputable def unitCntK (L : List Nat) : Nat :=
  unitCntR L (nat_lit 0) (Nat.pow (nat_lit 2) (List.length L))

@[expose] noncomputable def listBeq : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun x _ ih l => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => andB (Nat.beq x y) (ih ys)) l)

@[expose] noncomputable def solCntK (ps : List (Nat × Nat)) : Nat :=
  unitCntK (elimK ps (Nat.mul (nat_lit 25) (List.length ps)) (nat_lit 25)).2

@[expose] noncomputable def pevalK (c : Nat) (bs : List Bool) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b _ ih => Nat.xor (mmulK ih c) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) idK b)) bs

@[expose] noncomputable def polyBits (m : Nat) : List Bool :=
  Nat.rec (motive := fun _ => List Bool) List.nil
    (fun j acc => List.cons (bitK m (Nat.sub (nat_lit 5) j)) acc) (nat_lit 6)

@[expose] noncomputable def invK (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun m acc => Nat.add (Nat.mul acc (nat_lit 8)) (rankK (pevalK c (polyBits (Nat.succ m)))))
    (nat_lit 63)

@[expose] noncomputable def ordGoK (c : Nat) (k : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun acc => Nat.beq acc idK)
    (fun _ ih acc => letB acc fun a => andB (notB (Nat.beq a idK)) (ih (mmulK a c))) k

@[expose] noncomputable def ordK (c m : Nat) : Bool := ordGoK c (Nat.sub m 1) c

end CFSG.KC.Misc.GLM

end
