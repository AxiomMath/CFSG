module

public import Certificates.Data.Kernel.TcRes.Forest

public section

namespace CFSG.TcRes.TK

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def anyLt (c : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun m ih => orB (p m) ih) c

@[expose] noncomputable def dg (u m : Nat) : Nat :=
  Nat.mod (Nat.div u (Nat.pow (nat_lit 3) m)) (nat_lit 3)

@[expose] noncomputable def ldOK (u j : Nat) : Bool :=
  andB (Nat.ble (Nat.pow (nat_lit 3) j) u)
    (Nat.blt u (Nat.mul (nat_lit 2) (Nat.pow (nat_lit 3) j)))

@[expose] noncomputable def mPred (u j : Nat) : Bool :=
  andB (anyLt (nat_lit 6) fun i => andB (Nat.blt j i) (ldOK u i)) (Nat.beq (dg u j) (nat_lit 0))

@[expose] noncomputable def lowW (w c : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul w c)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def LOW12 : Nat := lowW (nat_lit 12) (nat_lit 729)

@[expose] noncomputable def LOW5 : Nat := lowW (nat_lit 5) (nat_lit 72)

@[expose] noncomputable def b2n (b : Bool) : Nat := Bool.rec (motive := fun _ => Nat) 0 1 b

@[expose] noncomputable def tabOK (U L M : Nat → Nat) (u : Nat) : Bool :=
  allLt (nat_lit 6) fun m =>
    andB (Nat.beq (fld (U m) (nat_lit 12) u) (dg u m))
    (andB (Nat.beq (fld (L m) (nat_lit 12) u) (b2n (ldOK u m)))
      (Nat.beq (fld (M m) (nat_lit 12) u) (b2n (mPred u m))))

@[expose] noncomputable def tabsOK (U L M : Nat → Nat) (i : Nat) : Bool :=
  allLt (nat_lit 81) fun j => tabOK U L M (Nat.add (Nat.mul (nat_lit 81) i) j)

@[expose] noncomputable def rcOK (RC : Nat → Nat) (V g : Nat) : Bool :=
  strictB (fld V (nat_lit 96) g) fun vg =>
  allLt (nat_lit 6) fun m =>
    Nat.beq (fld (RC m) (nat_lit 5) g)
      (Nat.mod (Nat.add (fld vg (nat_lit 16) m) (nat_lit 2)) (nat_lit 3))

@[expose] noncomputable def pwOK (RT REPS PAR PW k : Nat) : Bool :=
  strictB (Nat.land (Nat.shiftRight REPS (Nat.mul k (nat_lit 42))) M42) fun t =>
  strictB (fld PW (nat_lit 504) k) fun pw =>
  allLt (nat_lit 72) fun g =>
    Bool.rec (motive := fun _ => Bool)
      (strictB (fld PAR (nat_lit 16) g) fun e =>
        Nat.beq (fld pw (nat_lit 7) g)
          (rtv RT (tf t (Nat.shiftRight e (nat_lit 8))) (fld pw (nat_lit 7) (Nat.land e (nat_lit 255)))))
      (Nat.beq (fld pw (nat_lit 7) g) (tf t g))
      (Nat.blt g (nat_lit 6))

@[expose] noncomputable def zl (LOW x : Nat) : Nat :=
  strictN (Nat.add (Nat.land x (Nat.mul LOW (nat_lit 3)))
      (Nat.shiftRight (Nat.land x (Nat.mul LOW (nat_lit 28))) (nat_lit 2))) fun x1 =>
  strictN (Nat.add (Nat.add (Nat.land x1 (Nat.mul LOW (nat_lit 3)))
      (Nat.shiftRight (Nat.land x1 (Nat.mul LOW (nat_lit 28))) (nat_lit 2)))
      (Nat.mul LOW (nat_lit 8))) fun z =>
  strictN (Nat.land (Nat.shiftRight (Nat.sub z LOW) (nat_lit 3)) LOW) fun e1 =>
  strictN (Nat.land (Nat.shiftRight (Nat.sub z (Nat.mul LOW (nat_lit 3))) (nat_lit 3)) LOW) fun e3 =>
  strictN (Nat.land (Nat.shiftRight (Nat.sub z (Nat.mul LOW (nat_lit 4))) (nat_lit 3)) LOW) fun e4 =>
    Nat.lor (Nat.xor e1 LOW) (Nat.land e3 (Nat.xor e4 LOW))

@[expose] noncomputable def sOf (b : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 2) (nat_lit 1) (Nat.beq b (nat_lit 1))

@[expose] noncomputable def kj (U RC : Nat → Nat) (s γ j : Nat) : Nat :=
  zl LOW12
    (Nat.add (Nat.mul (fld (RC (nat_lit 0)) (nat_lit 5) γ) (U (nat_lit 0)))
    (Nat.add (Nat.mul (fld (RC (nat_lit 1)) (nat_lit 5) γ) (U (nat_lit 1)))
    (Nat.add (Nat.mul (fld (RC (nat_lit 2)) (nat_lit 5) γ) (U (nat_lit 2)))
    (Nat.add (Nat.mul (fld (RC (nat_lit 3)) (nat_lit 5) γ) (U (nat_lit 3)))
    (Nat.add (Nat.mul (fld (RC (nat_lit 4)) (nat_lit 5) γ) (U (nat_lit 4)))
    (Nat.add (Nat.mul (fld (RC (nat_lit 5)) (nat_lit 5) γ) (U (nat_lit 5)))
      (Nat.mul (Nat.sub (nat_lit 3) s) (U j))))))))

@[expose] noncomputable def kq (U RC : Nat → Nat) (REPS q : Nat) : Nat :=
  strictN (Nat.land (Nat.shiftRight REPS (Nat.mul (Nat.div q (nat_lit 3)) (nat_lit 42))) M42)
    fun t =>
  strictN (sOf (Nat.mod q (nat_lit 3))) fun s =>
    Nat.rec (motive := fun _ => Nat) LOW12
      (fun j ih => strictN ih fun a => Nat.land a (kj U RC s (tf t j) j)) (nat_lit 6)

@[expose] noncomputable def pop12 (x : Nat) : Nat := fld (Nat.mul x LOW12) (nat_lit 12) (nat_lit 728)

@[expose] noncomputable def npairs (L M : Nat → Nat) (K : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j ih => Nat.add (Nat.mul (pop12 (Nat.land K (L j))) (pop12 (Nat.land K (M j)))) ih)
    (nat_lit 6)

@[expose] noncomputable def M547 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 547)) (nat_lit 1)

@[expose] noncomputable def prec (LF : Nat → Nat) (p : Nat) : Nat :=
  Nat.land (Nat.shiftRight (LF (Nat.shiftRight p (nat_lit 4)))
    (Nat.mul (Nat.land p (nat_lit 15)) (nat_lit 547))) M547

@[expose] noncomputable def pu1 (e : Nat) : Nat := Nat.land e (nat_lit 1023)

@[expose] noncomputable def pu2 (e : Nat) : Nat :=
  Nat.land (Nat.shiftRight e (nat_lit 10)) (nat_lit 1023)

@[expose] noncomputable def pq (e : Nat) : Nat :=
  Nat.land (Nat.shiftRight e (nat_lit 20)) (nat_lit 127)

@[expose] noncomputable def lane1 (x u : Nat) : Bool := Nat.beq (fld x (nat_lit 12) u) (nat_lit 1)

@[expose] noncomputable def redOK (L M : Nat → Nat) (u1 u2 : Nat) : Bool :=
  anyLt (nat_lit 6) fun j => andB (lane1 (L j) u2) (lane1 (M j) u1)

@[expose] noncomputable def swStep (L M : Nat → Nat) (LF : Nat → Nat) (K q tot p prev : Nat)
    (k : Nat → Bool) : Bool :=
  strictB (prec LF p) fun e =>
  strictB (pu1 e) fun u1 =>
  strictB (pu2 e) fun u2 =>
  strictB (Nat.add (Nat.mul (nat_lit 729) u1) u2) fun key =>
    andB (Nat.blt p tot) (andB (Nat.beq (pq e) q) (andB (redOK L M u1 u2)
      (andB (Nat.blt prev key) (andB (lane1 K u1) (andB (lane1 K u2) (k key))))))

@[expose] noncomputable def swWalk (L M : Nat → Nat) (LF : Nat → Nat) (K q tot c : Nat) :
    Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih p prev => swStep L M LF K q tot p prev (ih (Nat.succ p))) c

@[expose] noncomputable def swOK (U RC L M : Nat → Nat) (LF : Nat → Nat) (REPS START q : Nat) :
    Bool :=
  strictB (kq U RC REPS q) fun K =>
  strictB (fld START (nat_lit 16) q) fun a =>
  strictB (fld START (nat_lit 16) (Nat.succ q)) fun e =>
    andB (Nat.beq (npairs L M K) (Nat.sub e a))
      (swWalk L M LF K q (fld START (nat_lit 16) (nat_lit 75)) (Nat.sub e a) a (nat_lit 0))

@[expose] noncomputable def dot5 (RC : Nat → Nat) (u : Nat) : Nat :=
  Nat.add (Nat.mul (dg u (nat_lit 0)) (RC (nat_lit 0)))
  (Nat.add (Nat.mul (dg u (nat_lit 1)) (RC (nat_lit 1)))
  (Nat.add (Nat.mul (dg u (nat_lit 2)) (RC (nat_lit 2)))
  (Nat.add (Nat.mul (dg u (nat_lit 3)) (RC (nat_lit 3)))
  (Nat.add (Nat.mul (dg u (nat_lit 4)) (RC (nat_lit 4)))
    (Nat.mul (dg u (nat_lit 5)) (RC (nat_lit 5)))))))

@[expose] noncomputable def squash (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun g ih => strictN ih fun a => Nat.lor (Nat.shiftLeft a (nat_lit 1))
      (Nat.land (Nat.shiftRight x (Nat.mul (Nat.sub (nat_lit 71) g) (nat_lit 5))) (nat_lit 1)))
    (nat_lit 72)

@[expose] noncomputable def kmask (RC : Nat → Nat) (u1 u2 : Nat) : Nat :=
  strictN (squash (zl LOW5 (dot5 RC u1))) fun a =>
  strictN (squash (zl LOW5 (dot5 RC u2))) fun b => Nat.land a b

@[expose] noncomputable def bit (m i : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) i))

@[expose] noncomputable def finOK (ph : Nat → Nat) (P mv C rt NB : Nat) : Bool :=
  orB (Nat.beq C (nat_lit 0))
    (strictB (Nat.land NB P) fun A =>
      andB (Nat.beq (Nat.land A C) A) (orB (Nat.beq mv (nat_lit 1)) (bit C (ph rt))))

@[expose] noncomputable def entWalk (ADJ : Nat) (ph : Nat → Nat) (P mv c : Nat) :
    Nat → Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
    (fun _ acc C rt NB => andB (finOK ph P mv C rt NB) (Nat.beq acc P))
    (fun _ ih rest acc C rt NB =>
      strictB (Nat.land rest (nat_lit 127)) fun g =>
      strictB (Nat.land (Nat.shiftRight rest (nat_lit 7)) (nat_lit 127)) fun pa =>
      strictB (fld ADJ (nat_lit 72) g) fun ag =>
      strictB (Nat.shiftLeft (nat_lit 1) g) fun bg =>
        andB (bit P g) (andB (notB (bit acc g))
          (Bool.rec (motive := fun _ => Bool)
            (andB (bit C pa) (andB (bit ag pa)
              (ih (Nat.shiftRight rest (nat_lit 14)) (Nat.lor acc bg) (Nat.lor C bg) rt
                (Nat.lor NB ag))))
            (andB (finOK ph P mv C rt NB)
              (ih (Nat.shiftRight rest (nat_lit 14)) (Nat.lor acc bg) bg g ag))
            (Nat.beq g pa)))) c

@[expose] noncomputable def phq (PW NEG q g : Nat) : Nat :=
  strictN (fld (fld PW (nat_lit 504) (Nat.div q (nat_lit 3))) (nat_lit 7) g) fun h =>
    Bool.rec (motive := fun _ => Nat) (fld NEG (nat_lit 7) h) h
      (Nat.beq (Nat.mod q (nat_lit 3)) (nat_lit 0))

@[expose] noncomputable def plOK (RC : Nat → Nat) (ADJ PW NEG e : Nat) : Bool :=
  strictB (kmask RC (pu1 e) (pu2 e)) fun P =>
  strictB (pq e) fun q =>
    entWalk ADJ (phq PW NEG q) P (Nat.land (Nat.shiftRight e (nat_lit 27)) (nat_lit 1))
      (Nat.land (Nat.shiftRight e (nat_lit 36)) (nat_lit 127)) (Nat.shiftRight e (nat_lit 43))
      (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def pleaf (RC : Nat → Nat) (LF : Nat → Nat) (ADJ PW NEG START L : Nat) :
    Bool :=
  strictB (fld START (nat_lit 16) (nat_lit 75)) fun tot =>
    Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
      (fun _ ih p rest =>
        andB (orB (Nat.ble tot p) (plOK RC ADJ PW NEG (Nat.land rest M547)))
          (ih (Nat.succ p) (Nat.shiftRight rest (nat_lit 547))))
      (nat_lit 16) (Nat.mul L (nat_lit 16)) (LF L)

end CFSG.TcRes.TK

end
