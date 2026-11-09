module

public import Certificates.Data.Kernel.OpsLayFill

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT

@[expose] noncomputable def mulEq (c : Lay) (X Y Z : Nat) : Bool := Nat.beq (c.mul X Y) Z

theorem mulEq_eq {c : Lay} {X Y Z : Nat} (h : mulEq c X Y Z = true) : c.mul X Y = Z :=
  Nat.eq_of_beq_eq_true h

theorem strictN_val (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem powN_succ (c : Lay) (f X e : Nat) : powN c (f + 1) X e =
    Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (CFSG.KC.Loop.strictN (c.mul X X) fun X2 =>
          CFSG.KC.Loop.strictN (powN c f X2 (Nat.div e 2)) fun Y =>
            Bool.rec (motive := fun _ => Nat) Y (c.mul X Y) (Nat.beq (Nat.mod e 2) 1))
        X (Nat.beq e 1))
      c.ONE (Nat.beq e 0) := rfl

theorem powK_one (c : Lay) (X : Nat) : powK c X 1 = X := rfl

theorem powK_two (c : Lay) (X : Nat) : powK c X 2 = c.mul X X := by
  have e : powK c X 2 = powN c (16 + 1) X 2 := rfl
  rw [e, powN_succ, strictN_val, strictN_val]
  rfl

theorem powK_three (c : Lay) (X : Nat) : powK c X 3 = c.mul X (c.mul X X) := by
  have e : powK c X 3 = powN c (16 + 1) X 3 := rfl
  rw [e, powN_succ, strictN_val, strictN_val]
  rfl

theorem factL1_ord3 {c : Lay} {R : List Nat} {n r X2 : Nat} (hr : decide (r < n) = true)
    (h1 : mulEq c (getR c R r) (getR c R r) X2 = true)
    (h2 : mulEq c (getR c R r) X2 c.ONE = true) :
    factL1 c R n (.ord r 3) = true := by
  have e := mulEq_eq h2
  rw [← mulEq_eq h1] at e
  simp only [factL1, Bool.and_eq_true, hr, powK_three, e, Nat.beq_refl]
  decide

theorem factL1_comm {c : Lay} {R : List Nat} {n a b P : Nat}
    (hok : (wordOK n [(a, 1), (b, 1)] && wordOK n [(b, 1), (a, 1)]) = true)
    (h1 : mulEq c (getR c R a) (getR c R b) P = true)
    (h2 : mulEq c (getR c R b) (getR c R a) P = true) :
    factL1 c R n (.eq [(a, 1), (b, 1)] [(b, 1), (a, 1)]) = true := by
  simp only [factL1, evalWL1, powK_one, Bool.and_eq_true] at hok ⊢
  rw [mulEq_eq h1, mulEq_eq h2]
  exact ⟨hok, Nat.beq_refl P⟩

theorem factL1_conj1 {c : Lay} {R : List Nat} {n h a e b f U W P : Nat}
    (hok : (decide (h < n) && wordOK n [(a, e)] && wordOK n [(b, f)]) = true)
    (hU : powK c (getR c R a) e = U) (hW : powK c (getR c R b) f = W)
    (h1 : mulEq c (getR c R h) U P = true) (h2 : mulEq c W (getR c R h) P = true) :
    factL1 c R n (.conj h [(a, e)] [(b, f)]) = true := by
  simp only [factL1, evalWL1, Bool.and_eq_true] at hok ⊢
  rw [hU, hW, mulEq_eq h1, mulEq_eq h2]
  exact ⟨hok, Nat.beq_refl P⟩

end CFSG.KC.OpsLayK

end
