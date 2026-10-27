module

public import Certificates.Data.Kernel.TcRes.Trans

public section

namespace CFSG.TcRes.TK

@[expose] noncomputable def dg5 (u m : Nat) : Nat :=
  Nat.mod (Nat.div u (Nat.pow (nat_lit 5) m)) (nat_lit 5)

@[expose] noncomputable def ld5OK (c j : Nat) : Bool :=
  andB (Nat.ble (Nat.pow (nat_lit 5) j) c) (Nat.blt c (Nat.mul (nat_lit 2) (Nat.pow (nat_lit 5) j)))

@[expose] noncomputable def m5Pred (c j : Nat) : Bool :=
  andB (anyLt (nat_lit 4) fun i => andB (Nat.blt j i) (ld5OK c i)) (Nat.beq (dg5 c j) (nat_lit 0))

@[expose] noncomputable def tab5OK (U L M : Nat → Nat) (c : Nat) : Bool :=
  allLt (nat_lit 4) fun m =>
    andB (Nat.beq (fld (U m) (nat_lit 12) c) (dg5 c m))
    (andB (Nat.beq (fld (L m) (nat_lit 12) c) (b2n (ld5OK c m)))
      (Nat.beq (fld (M m) (nat_lit 12) c) (b2n (m5Pred c m))))

@[expose] noncomputable def tabs5OK (U L M : Nat → Nat) (i : Nat) : Bool :=
  allLt (nat_lit 125) fun j => tab5OK U L M (Nat.add (Nat.mul (nat_lit 125) i) j)

@[expose] noncomputable def rc5OK (RC : Nat → Nat) (V g : Nat) : Bool :=
  strictB (fld V (nat_lit 128) g) fun vg =>
  allLt (nat_lit 8) fun m =>
    Nat.beq (fld (RC m) (nat_lit 8) g) (Nat.mod (Nat.add (fld vg (nat_lit 16) m) (nat_lit 3)) (nat_lit 5))

@[expose] noncomputable def pw8OK (RTs : Nat → Nat) (T0 PAR PW : Nat) : Bool :=
  allLt (nat_lit 240) fun g =>
    Bool.rec (motive := fun _ => Bool)
      (strictB (fld PAR (nat_lit 16) g) fun e =>
        Nat.beq (fld PW (nat_lit 8) g)
          (fld (RTs (fld T0 (nat_lit 8) (Nat.shiftRight e (nat_lit 8)))) (nat_lit 8)
            (fld PW (nat_lit 8) (Nat.land e (nat_lit 255)))))
      (Nat.beq (fld PW (nat_lit 8) g) (fld T0 (nat_lit 8) g))
      (Nat.blt g (nat_lit 8))

@[expose] noncomputable def amj (RC : Nat → Nat) (T0 r m j : Nat) : Nat :=
  Nat.mod (Nat.add (fld (RC m) (nat_lit 8) (fld T0 (nat_lit 8) j))
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.sub (nat_lit 5) r) (Nat.beq m j))) (nat_lit 5)

@[expose] noncomputable def sumLt (c : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i ih => strictN ih fun a => Nat.add a (f i)) c

@[expose] noncomputable def kOK (RC : Nat → Nat) (T0 B PV MW r : Nat) : Bool :=
  andB (allLt (nat_lit 4) fun i => strictB (fld B (nat_lit 20) i) fun b =>
      andB (allLt (nat_lit 8) fun j =>
          Nat.beq (Nat.mod (sumLt (nat_lit 8) fun m => Nat.mul (dg5 b m) (amj RC T0 r m j)) (nat_lit 5))
            (nat_lit 0))
        (allLt (nat_lit 4) fun k => strictB (fld PV (nat_lit 3) k) fun pk =>
          andB (Nat.blt pk (nat_lit 8))
            (Nat.beq (dg5 b pk) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq i k)))))
    (allLt (nat_lit 4) fun a => allLt (nat_lit 4) fun b =>
      Nat.beq (Nat.mod (sumLt (nat_lit 4) fun c =>
          Nat.mul (amj RC T0 r (fld MW (nat_lit 3) a) (fld MW (nat_lit 3) (Nat.add (nat_lit 4) c)))
            (fld MW (nat_lit 3) (Nat.add (nat_lit 8) (Nat.add (Nat.mul (nat_lit 4) c) b)))) (nat_lit 5))
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq a b)))

@[expose] noncomputable def LOW625 : Nat := lowW (nat_lit 12) (nat_lit 625)

@[expose] noncomputable def pop625 (x : Nat) : Nat := fld (Nat.mul x LOW625) (nat_lit 12) (nat_lit 624)

@[expose] noncomputable def M448 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 448)) (nat_lit 1)

@[expose] noncomputable def prec5 (LF : Nat → Nat) (p : Nat) : Nat :=
  Nat.land (Nat.shiftRight (LF (Nat.shiftRight p (nat_lit 4)))
    (Nat.mul (Nat.land p (nat_lit 15)) (nat_lit 448))) M448

@[expose] noncomputable def sw5Walk (L M LF : Nat → Nat) (s c : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih p prev =>
      strictB (prec5 LF p) fun e =>
      strictB (Nat.land e (nat_lit 1023)) fun c1 =>
      strictB (Nat.land (Nat.shiftRight e (nat_lit 10)) (nat_lit 1023)) fun c2 =>
      strictB (Nat.add (Nat.mul (nat_lit 625) c1) c2) fun key =>
        andB (Nat.beq (Nat.land (Nat.shiftRight e (nat_lit 20)) (nat_lit 1)) s)
          (andB (anyLt (nat_lit 4) fun j => andB (lane1 (L j) c2) (lane1 (M j) c1))
            (andB (Nat.blt prev key) (ih (Nat.succ p) key)))) c

@[expose] noncomputable def sw5OK (L M LF : Nat → Nat) (s : Nat) : Bool :=
  andB (Nat.beq (sumLt (nat_lit 4) fun j => Nat.mul (pop625 (L j)) (pop625 (M j))) (nat_lit 806))
    (sw5Walk L M LF s (nat_lit 806) (Nat.mul (nat_lit 806) s) (nat_lit 0))

@[expose] noncomputable def um (B c m : Nat) : Nat :=
  Nat.mod (sumLt (nat_lit 4) fun i => Nat.mul (dg5 c i) (dg5 (fld B (nat_lit 20) i) m)) (nat_lit 5)

@[expose] noncomputable def LOW8 : Nat := lowW (nat_lit 8) (nat_lit 240)

@[expose] noncomputable def dot8 (RC : Nat → Nat) (B c : Nat) : Nat :=
  sumLt (nat_lit 8) fun m => Nat.mul (um B c m) (RC m)

@[expose] noncomputable def zl5 (x : Nat) : Nat :=
  strictN (Nat.add (Nat.land x (Nat.mul LOW8 (nat_lit 15)))
      (Nat.land (Nat.shiftRight x (nat_lit 4)) (Nat.mul LOW8 (nat_lit 15)))) fun x1 =>
  strictN (Nat.add (Nat.add (Nat.land x1 (Nat.mul LOW8 (nat_lit 15)))
      (Nat.land (Nat.shiftRight x1 (nat_lit 4)) (Nat.mul LOW8 (nat_lit 15)))) (Nat.mul LOW8 (nat_lit 16)))
    fun z =>
  strictN (Nat.land (Nat.shiftRight (Nat.sub z LOW8) (nat_lit 4)) LOW8) fun g1 =>
  strictN (Nat.land (Nat.shiftRight (Nat.sub z (Nat.mul LOW8 (nat_lit 5))) (nat_lit 4)) LOW8) fun g5 =>
  strictN (Nat.land (Nat.shiftRight (Nat.sub z (Nat.mul LOW8 (nat_lit 6))) (nat_lit 4)) LOW8) fun g6 =>
  strictN (Nat.land (Nat.shiftRight (Nat.sub z (Nat.mul LOW8 (nat_lit 10))) (nat_lit 4)) LOW8) fun g10 =>
  strictN (Nat.land (Nat.shiftRight (Nat.sub z (Nat.mul LOW8 (nat_lit 11))) (nat_lit 4)) LOW8) fun g11 =>
  strictN (Nat.land (Nat.shiftRight (Nat.sub z (Nat.mul LOW8 (nat_lit 15))) (nat_lit 4)) LOW8) fun g15 =>
    Nat.lor (Nat.xor g1 LOW8) (Nat.lor (Nat.land g5 (Nat.xor g6 LOW8))
      (Nat.lor (Nat.land g10 (Nat.xor g11 LOW8)) g15))

@[expose] noncomputable def squash8 (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => strictN ih fun a => Nat.lor a (Nat.shiftLeft
      (Nat.land (Nat.shiftRight (Nat.mul (fld x (nat_lit 64) i) (nat_lit 72624976668147840))
        (nat_lit 56)) (nat_lit 255)) (Nat.mul (nat_lit 8) i)))
    (nat_lit 30)

@[expose] noncomputable def kmask5 (RC : Nat → Nat) (B c1 c2 : Nat) : Nat :=
  strictN (squash8 (zl5 (dot8 RC B c1))) fun a =>
  strictN (squash8 (zl5 (dot8 RC B c2))) fun b => Nat.land a b

@[expose] noncomputable def entWalk8 (ADJ : Nat) (ph : Nat → Nat) (P mv c : Nat) :
    Nat → Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
    (fun _ acc C rt NB => andB (finOK ph P mv C rt NB) (Nat.beq acc P))
    (fun _ ih rest acc C rt NB =>
      strictB (Nat.land rest (nat_lit 255)) fun g =>
      strictB (Nat.land (Nat.shiftRight rest (nat_lit 8)) (nat_lit 255)) fun pa =>
      strictB (fld ADJ (nat_lit 240) g) fun ag =>
      strictB (Nat.shiftLeft (nat_lit 1) g) fun bg =>
        andB (bit P g) (andB (notB (bit acc g))
          (Bool.rec (motive := fun _ => Bool)
            (andB (bit C pa) (andB (bit ag pa)
              (ih (Nat.shiftRight rest (nat_lit 16)) (Nat.lor acc bg) (Nat.lor C bg) rt
                (Nat.lor NB ag))))
            (andB (finOK ph P mv C rt NB)
              (ih (Nat.shiftRight rest (nat_lit 16)) (Nat.lor acc bg) bg g ag))
            (Nat.beq g pa)))) c

@[expose] noncomputable def pl5OK (RC BS : Nat → Nat) (ADJ PW e : Nat) : Bool :=
  strictB (BS (Nat.land (Nat.shiftRight e (nat_lit 20)) (nat_lit 1))) fun B =>
  strictB (kmask5 RC B (Nat.land e (nat_lit 1023)) (Nat.land (Nat.shiftRight e (nat_lit 10)) (nat_lit 1023)))
    fun P =>
    entWalk8 ADJ (fun g => fld PW (nat_lit 8) g) P (Nat.land (Nat.shiftRight e (nat_lit 21)) (nat_lit 1))
      (Nat.land (Nat.shiftRight e (nat_lit 34)) (nat_lit 63)) (Nat.shiftRight e (nat_lit 40))
      (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def pleaf5 (RC BS LF : Nat → Nat) (ADJ PW L : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih p rest =>
      andB (orB (Nat.ble (nat_lit 1612) p) (pl5OK RC BS ADJ PW (Nat.land rest M448)))
        (ih (Nat.succ p) (Nat.shiftRight rest (nat_lit 448))))
    (nat_lit 16) (Nat.mul L (nat_lit 16)) (LF L)

end CFSG.TcRes.TK

end
