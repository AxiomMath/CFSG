module

public import Certificates.Data.Kernel.TcRes.Defs

public section

namespace CFSG.TcRes.TK

@[expose] noncomputable def strictN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def rtv (RT g v : Nat) : Nat :=
  Nat.land (Nat.shiftRight RT (Nat.mul (Nat.add (Nat.mul g (nat_lit 72)) v) (nat_lit 7)))
    (nat_lit 127)

@[expose] noncomputable def tf (t j : Nat) : Nat :=
  Nat.land (Nat.shiftRight t (Nat.mul j (nat_lit 7))) (nat_lit 127)

@[expose] noncomputable def cjA (RT t i a : Nat) : Nat :=
  Nat.lor (rtv RT i (rtv RT a (tf t (nat_lit 0))))
  (Nat.lor (Nat.shiftLeft (rtv RT i (rtv RT a (tf t (nat_lit 1)))) (nat_lit 7))
  (Nat.lor (Nat.shiftLeft (rtv RT i (rtv RT a (tf t (nat_lit 2)))) (nat_lit 14))
  (Nat.lor (Nat.shiftLeft (rtv RT i (rtv RT a (tf t (nat_lit 3)))) (nat_lit 21))
  (Nat.lor (Nat.shiftLeft (rtv RT i (rtv RT a (tf t (nat_lit 4)))) (nat_lit 28))
    (Nat.shiftLeft (rtv RT i (rtv RT a (tf t (nat_lit 5)))) (nat_lit 35))))))

@[expose] noncomputable def cj (RT t i : Nat) : Nat := strictN (tf t i) (cjA RT t i)

@[expose] noncomputable def lm (RT i t : Nat) : Nat :=
  Nat.lor (rtv RT i (tf t (nat_lit 0)))
  (Nat.lor (Nat.shiftLeft (rtv RT i (tf t (nat_lit 1))) (nat_lit 7))
  (Nat.lor (Nat.shiftLeft (rtv RT i (tf t (nat_lit 2))) (nat_lit 14))
  (Nat.lor (Nat.shiftLeft (rtv RT i (tf t (nat_lit 3))) (nat_lit 21))
  (Nat.lor (Nat.shiftLeft (rtv RT i (tf t (nat_lit 4))) (nat_lit 28))
    (Nat.shiftLeft (rtv RT i (tf t (nat_lit 5))) (nat_lit 35))))))

@[expose] noncomputable def M42 : Nat := nat_lit 4398046511103

@[expose] noncomputable def M67 : Nat := nat_lit 147573952589676412927

@[expose] noncomputable def ent (LF : Nat → Nat) (p : Nat) : Nat :=
  Nat.land (Nat.shiftRight (LF (Nat.shiftRight p (nat_lit 6)))
    (Nat.mul (Nat.land p (nat_lit 63)) (nat_lit 67))) M67

@[expose] noncomputable def keyOf (e : Nat) : Nat := Nat.land e M42

@[expose] noncomputable def depOf (e : Nat) : Nat :=
  Nat.land (Nat.shiftRight e (nat_lit 42)) (nat_lit 63)

@[expose] noncomputable def parOf (e : Nat) : Nat :=
  Nat.land (Nat.shiftRight e (nat_lit 48)) (nat_lit 65535)

@[expose] noncomputable def genOf (e : Nat) : Nat := Nat.shiftRight e (nat_lit 64)

@[expose] noncomputable def fparOK (RT k g d pe : Nat) : Bool :=
  andB (Nat.beq (Nat.succ (depOf pe)) d)
    (andB (Nat.blt g (nat_lit 6)) (Nat.beq k (cj RT (keyOf pe) g)))

@[expose] noncomputable def recOK (RT : Nat) (LF : Nat → Nat) (REPS e : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (andB (Nat.blt (parOf e) (nat_lit 51840))
      (strictB (ent LF (parOf e)) (fparOK RT (keyOf e) (genOf e) (depOf e))))
    (andB (Nat.blt (parOf e) (nat_lit 25))
      (Nat.beq (keyOf e) (Nat.land (Nat.shiftRight REPS (Nat.mul (parOf e) (nat_lit 42))) M42)))
    (Nat.beq (depOf e) (nat_lit 0))

@[expose] noncomputable def stepOK (RT : Nat) (LF : Nat → Nat) (REPS e prev : Nat)
    (k : Nat → Bool) : Bool :=
  andB (Nat.blt prev (keyOf e)) (andB (recOK RT LF REPS e) (k (keyOf e)))

@[expose] noncomputable def walk (RT : Nat) (LF : Nat → Nat) (REPS c : Nat) :
    Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih rest prev => strictB (Nat.land rest M67) fun e =>
      stepOK RT LF REPS e prev (ih (Nat.shiftRight rest (nat_lit 67)))) c

@[expose] noncomputable def prevKey (LF : Nat → Nat) (L : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l _ => keyOf (ent LF (Nat.add (Nat.mul l (nat_lit 64)) (nat_lit 63)))) L

@[expose] noncomputable def leafOK (RT : Nat) (LF : Nat → Nat) (REPS L : Nat) : Bool :=
  walk RT LF REPS (nat_lit 64) (LF L) (prevKey LF L)

@[expose] noncomputable def wordOK (RT goal c : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ t => Nat.beq t goal)
    (fun _ ih u t => strictB (Nat.land u (nat_lit 7)) fun l =>
      andB (Nat.blt l (nat_lit 6))
        (strictB (lm RT l t) fun t' => ih (Nat.shiftRight u (nat_lit 3)) t')) c

@[expose] noncomputable def repOK (RT REPS WRD k : Nat) : Bool :=
  strictB (Nat.land (Nat.shiftRight WRD (Nat.mul k (nat_lit 128)))
      (nat_lit 340282366920938463463374607431768211455)) fun e =>
    wordOK RT (Nat.land (Nat.shiftRight REPS (Nat.mul k (nat_lit 42))) M42)
      (Nat.land e (nat_lit 63)) (Nat.shiftRight e (nat_lit 6)) (nat_lit 172878758016)

end CFSG.TcRes.TK

end
