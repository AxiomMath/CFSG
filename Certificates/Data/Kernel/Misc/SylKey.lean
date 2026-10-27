module

public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.KC.SylKey

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] def rd (c i : Nat) : Nat :=
  Nat.land (Nat.shiftRight c (Nat.mul (nat_lit 4) i)) (nat_lit 15)

@[expose] def cdF (f : Nat → Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
    (Nat.add (f (nat_lit 0)) (Nat.shiftLeft (f (nat_lit 1)) (nat_lit 4)))
    (Nat.shiftLeft (f (nat_lit 2)) (nat_lit 8))) (Nat.shiftLeft (f (nat_lit 3)) (nat_lit 12)))
    (Nat.shiftLeft (f (nat_lit 4)) (nat_lit 16))) (Nat.shiftLeft (f (nat_lit 5)) (nat_lit 20)))
    (Nat.shiftLeft (f (nat_lit 6)) (nat_lit 24))) (Nat.shiftLeft (f (nat_lit 7)) (nat_lit 28)))
    (Nat.shiftLeft (f (nat_lit 8)) (nat_lit 32))) (Nat.shiftLeft (f (nat_lit 9)) (nat_lit 36)))
    (Nat.shiftLeft (f (nat_lit 10)) (nat_lit 40))) (Nat.shiftLeft (f (nat_lit 11)) (nat_lit 44))

@[expose] def cd (σ : Equiv.Perm (Fin 12)) : Nat :=
  cdF fun i => if h : i < 12 then (σ ⟨i, h⟩ : Nat) else 0

@[expose] def mulK (a b : Nat) : Nat := cdF fun i => rd a (rd b i)

@[expose] def idK : Nat := nat_lit 205163983024656

@[expose] def pw (x : Nat) (e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idK (fun _ ih => mulK x ih) e

@[expose] noncomputable def kgo (x k : Nat) (s : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun m c => Bool.and (Nat.beq m k) (Nat.beq (mulK x c) idK))
    (fun _ ih m c => strictB (mulK x c) fun y =>
      strictB (Bool.rec (motive := fun _ => Nat) y m (Nat.ble m y)) fun m' => ih m' y) s

@[expose] noncomputable def keyB (p k x : Nat) : Bool :=
  strictB x fun x => Bool.and (Bool.not (Nat.beq x idK)) (kgo x k (Nat.sub p (nat_lit 2)) x x)

@[expose] def lk (T i : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul (nat_lit 48) i)) (nat_lit 281474976710655)

@[expose] noncomputable def entB (p NT NIT RT : Nat) (e : Nat × Nat) : Bool :=
  Bool.and (Nat.blt (Nat.shiftRight e.1 (nat_lit 7)) (nat_lit 54))
    (Bool.and (Nat.blt (Nat.land e.1 (nat_lit 127)) (nat_lit 80))
      (keyB p e.2 (mulK (lk NT (Nat.shiftRight e.1 (nat_lit 7)))
        (mulK (lk RT (Nat.land e.1 (nat_lit 127))) (lk NIT (Nat.shiftRight e.1 (nat_lit 7)))))))

@[expose] noncomputable def allE (p NT NIT RT : Nat) (E : List (Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih prev => Bool.and (Nat.blt prev e.2) (Bool.and (entB p NT NIT RT e) (ih e.2))) E

@[expose] def pinB (T : Nat) (L : List (Equiv.Perm (Fin 12))) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun σ _ ih i => Bool.and (Nat.beq (lk T i) (cd σ)) (ih (Nat.succ i))) L

@[expose] def gK (g0 g1 g2 z : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) g2 g1 (Nat.beq z 1)) g0
    (Nat.beq z 0)

@[expose] def wev (g0 g1 g2 : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idK (fun z _ ih => mulK (gK g0 g1 g2 z) ih) w

@[expose] def wB (g0 g1 g2 T : Nat) (W : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih i => Bool.and (Nat.beq (wev g0 g1 g2 w) (lk T i)) (ih (Nat.succ i))) W

@[expose] noncomputable def nrmB (g0 g1 g2 r : Nat) (X : List (List Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun xe _ ih prev => strictB (wev g0 g1 g2 xe.1) fun x =>
      Bool.and (Nat.blt prev x) (Bool.and (Nat.beq (mulK x r) (mulK (pw r xe.2) x)) (ih x))) X

@[expose] def ordB (p x : Nat) : Bool := Bool.and (Bool.not (Nat.beq x idK)) (Nat.beq (pw x p) idK)

end CFSG.KC.SylKey

end
