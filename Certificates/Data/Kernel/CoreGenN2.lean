module

public import Certificates.Data.Kernel.CoreGenN

public section

namespace CFSG.KC.OpsMN

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsK CFSG.AGLEmbedding.R3

variable {V : Type} (O : Ops Nat V)

@[expose] noncomputable def stepN2 (R : List Nat) (k : List Nat → Bool) (op : Op) : Bool :=
  Op.rec (motive := fun _ => Bool)
    (fun i j t => forceB (O.mul (getN R i) (getN R j)) fun a => k (R.set t a))
    (fun e i t => forceB (powN O (Nat.succ e) (getN R i) e) fun a => k (R.set t a)) op

@[expose] noncomputable def runN2 (prog : List Op) : List Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → (List Nat → Bool) → Bool)
    (fun R k => k R) (fun op _ ih R k => stepN2 O R (fun R' => ih R' k) op) prog

@[expose] noncomputable def coreGenN2 (A B nregs : Nat) (prog : List Op) (D : RSpec) : Bool :=
  runN2 O prog (initN O A B nregs) fun R => certN O R ⟨nregs, prog, D.facts⟩ &&
    O.eq (getN R D.rA) A && O.eq (getN R D.rB) B

theorem forceB_eq2 (y : Nat) (k : Nat → Bool) : forceB y k = k y := by cases y <;> rfl

theorem forceL_eq2 : ∀ (xs : List Nat) (k : List Nat → Bool), forceL xs k = k xs
  | [], _ => rfl
  | x :: xs, k => by
    show forceB x (fun x' => forceL xs fun l => k (x' :: l)) = k (x :: xs)
    rw [forceB_eq2, forceL_eq2 xs]

theorem stepN_eq2 (R : List Nat) (k : List Nat → Bool) (op : Op) :
    stepN O R k op = stepN2 O R k op := by
  cases op with
  | mul i j t =>
    show forceB (O.mul (getN R i) (getN R j)) (fun a => forceL (R.set t a) k) =
      forceB (O.mul (getN R i) (getN R j)) (fun a => k (R.set t a))
    simp only [forceL_eq2]
  | pow e i t =>
    show forceB (powN O (Nat.succ e) (getN R i) e) (fun a => forceL (R.set t a) k) =
      forceB (powN O (Nat.succ e) (getN R i) e) (fun a => k (R.set t a))
    simp only [forceL_eq2]

theorem runN_eq2 : ∀ (prog : List Op) (R : List Nat) (k : List Nat → Bool),
    runN O prog R k = runN2 O prog R k
  | [], _, _ => rfl
  | op :: prog, R, k => by
    show stepN O R (fun R' => runN O prog R' k) op = stepN2 O R (fun R' => runN2 O prog R' k) op
    rw [stepN_eq2]
    have e : (fun R' => runN O prog R' k) = (fun R' => runN2 O prog R' k) :=
      funext fun R' => runN_eq2 prog R' k
    rw [e]

theorem coreGenN_eq2 (A B nregs : Nat) (prog : List Op) (D : RSpec) :
    coreGenN O A B nregs prog D = coreGenN2 O A B nregs prog D := by
  unfold coreGenN coreGenN2 regsN
  rw [runN_eq2]

@[expose] noncomputable def regGetK (R : List Nat) (r : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih r => Nat.rec (motive := fun _ => Nat) a (fun r' _ => ih r') r) R r
@[expose] noncomputable def regSetK (R : List Nat) (t a : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun b bs ih t => Nat.rec (motive := fun _ => List Nat) (a :: bs) (fun t' _ => b :: ih t') t) R t
@[expose] noncomputable def evalWN3 (R : List Nat) (w : Word) : Nat :=
  List.rec (motive := fun _ => Nat) O.one
    (fun p _ ih => O.mul (powN O (Nat.succ p.2) (regGetK R p.1) p.2) ih) w
@[expose] noncomputable def factN3 (R : List Nat) (n : Nat) : MFact → Bool
  | .ord r e => decide (r < n) && decide (0 < e) &&
      O.eq (powN O (Nat.succ e) (regGetK R r) e) O.one
  | .conj h u w => decide (h < n) && wordLt n u && wordLt n w &&
      O.eq (O.mul (regGetK R h) (evalWN3 O R u)) (O.mul (evalWN3 O R w) (regGetK R h))
  | .ne w₁ w₂ t => wordLt n w₁ && wordLt n w₂ &&
      O.vne (O.vmul (O.unit t) (evalWN3 O R w₁)) (O.vmul (O.unit t) (evalWN3 O R w₂))
  | .eq w₁ w₂ => wordLt n w₁ && wordLt n w₂ && O.eq (evalWN3 O R w₁) (evalWN3 O R w₂)
@[expose] noncomputable def stepN3 (R : List Nat) (k : List Nat → Bool) (op : Op) : Bool :=
  Op.rec (motive := fun _ => Bool)
    (fun i j t => forceB (O.mul (regGetK R i) (regGetK R j)) fun a => k (regSetK R t a))
    (fun e i t => forceB (powN O (Nat.succ e) (regGetK R i) e) fun a => k (regSetK R t a)) op
@[expose] noncomputable def runN3 (prog : List Op) : List Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → (List Nat → Bool) → Bool)
    (fun R k => k R) (fun op _ ih R k => stepN3 O R (fun R' => ih R' k) op) prog

theorem regGetK_eq : ∀ (R : List Nat) (r : Nat), regGetK R r = getN R r
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: R, r + 1 => by
    show regGetK R r = getN (a :: R) (r + 1)
    rw [regGetK_eq R r]
    rfl
theorem regSetK_eq : ∀ (R : List Nat) (t a : Nat), regSetK R t a = R.set t a
  | [], t, _ => by cases t <;> rfl
  | _ :: _, 0, _ => rfl
  | b :: R, t + 1, a => by
    show b :: regSetK R t a = (b :: R).set (t + 1) a
    rw [regSetK_eq R t a]
    rfl
theorem evalWN3_eq (R : List Nat) : ∀ w : Word, evalWN3 O R w = evalWN O R w
  | [] => rfl
  | (r, e) :: w => by
    show O.mul (powN O (Nat.succ e) (regGetK R r) e) (evalWN3 O R w) = evalWN O R ((r, e) :: w)
    rw [regGetK_eq, evalWN3_eq R w]
    rfl
theorem factN3_eq (R : List Nat) (n : Nat) (f : MFact) : factN3 O R n f = factN O R n f := by
  cases f <;> simp only [factN3, factN, evalWN3_eq, regGetK_eq]
theorem stepN2_eq3 (R : List Nat) (k : List Nat → Bool) (op : Op) :
    stepN2 O R k op = stepN3 O R k op := by
  cases op with
  | mul i j t =>
    show forceB (O.mul (getN R i) (getN R j)) (fun a => k (R.set t a)) =
      forceB (O.mul (regGetK R i) (regGetK R j)) (fun a => k (regSetK R t a))
    simp only [regGetK_eq, regSetK_eq]
  | pow e i t =>
    show forceB (powN O (Nat.succ e) (getN R i) e) (fun a => k (R.set t a)) =
      forceB (powN O (Nat.succ e) (regGetK R i) e) (fun a => k (regSetK R t a))
    simp only [regGetK_eq, regSetK_eq]
theorem runN2_eq3 : ∀ (prog : List Op) (R : List Nat) (k : List Nat → Bool),
    runN2 O prog R k = runN3 O prog R k
  | [], _, _ => rfl
  | op :: prog, R, k => by
    show stepN2 O R (fun R' => runN2 O prog R' k) op = stepN3 O R (fun R' => runN3 O prog R' k) op
    rw [stepN2_eq3]
    have e : (fun R' => runN2 O prog R' k) = (fun R' => runN3 O prog R' k) :=
      funext fun R' => runN2_eq3 prog R' k
    rw [e]

@[expose] noncomputable def certN3 (R : List Nat) (C : MCert) : Bool :=
  decide (2 ≤ C.nregs) && C.prog.all (Op.lt C.nregs) && C.facts.all (factN3 O R C.nregs)

@[expose] noncomputable def coreGenN3 (A B nregs : Nat) (prog : List Op) (D : RSpec) : Bool :=
  runN3 O prog (initN O A B nregs) fun R => certN3 O R ⟨nregs, prog, D.facts⟩ &&
    O.eq (regGetK R D.rA) A && O.eq (regGetK R D.rB) B

theorem certN3_eq (R : List Nat) (C : MCert) : certN3 O R C = certN O R C := by
  unfold certN3 certN
  rw [show factN3 O R C.nregs = factN O R C.nregs from funext (factN3_eq O R C.nregs)]

theorem coreGenN_eq3 (A B nregs : Nat) (prog : List Op) (D : RSpec) :
    coreGenN O A B nregs prog D = coreGenN3 O A B nregs prog D := by
  rw [coreGenN_eq2]
  unfold coreGenN2 coreGenN3
  rw [runN2_eq3]
  have e : (fun R => certN3 O R ⟨nregs, prog, D.facts⟩ && O.eq (regGetK R D.rA) A &&
      O.eq (regGetK R D.rB) B) = (fun R => certN O R ⟨nregs, prog, D.facts⟩ && O.eq (getN R D.rA) A &&
      O.eq (getN R D.rB) B) := by
    funext R
    rw [certN3_eq, regGetK_eq, regGetK_eq]
  rw [e]

end CFSG.KC.OpsMN

end
