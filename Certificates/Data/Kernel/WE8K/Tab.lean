module

public import Certificates.Data.Kernel.WE8K.Defs
public import Certificates.Data.CFSGNative.Chevalley.SteinbergBIWE8Native

public section

namespace CFSG.KC.WE8K

open CFSG.KC.Loop CFSG.LieType.Chevalley.WE8.Native

@[expose] noncomputable def all8 (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => bAnd(f k, ih)) (nat_lit 8)

@[expose] noncomputable def sum8 (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k ih => Nat.add (f k) ih) (nat_lit 8)

@[expose] noncomputable def l16 (x i : Nat) : Nat := fld(x, Nat.shiftLeft i (nat_lit 4), nat_lit 0xFFFF)

@[expose] noncomputable def uA (T a : Nat) : Nat :=
  fld(T, Nat.shiftLeft a (nat_lit 8), nat_lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)

@[expose] noncomputable def vA (T a : Nat) : Nat :=
  fld(T, Nat.add (Nat.shiftLeft a (nat_lit 8)) (nat_lit 128), nat_lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)

@[expose] noncomputable def dgT (T a i : Nat) : Nat := l16 (uA T a) i

@[expose] noncomputable def pT (T a i : Nat) : Nat := l16 (vA T a) (Nat.sub (nat_lit 7) i)

@[expose] noncomputable def REP16 : Nat := nat_lit 0x00010001000100010001000100010001

@[expose] noncomputable def dotT (T b a : Nat) : Nat :=
  fld(Nat.mul (uA T b) (vA T a), nat_lit 112, nat_lit 0xFFFF)

@[expose] noncomputable def sdT (T b : Nat) : Nat := fld(Nat.mul (uA T b) REP16, nat_lit 112, nat_lit 0xFFFF)

@[expose] noncomputable def spT (T a : Nat) : Nat := fld(Nat.mul (vA T a) REP16, nat_lit 112, nat_lit 0xFFFF)

@[expose] noncomputable def ipIs (T b a xp xm : Nat) : Bool :=
  Nat.beq (Nat.add (Nat.add (dotT T b a) (nat_lit 128)) xm)
    (Nat.add (Nat.add (Nat.mul (nat_lit 2) (sdT T b)) (Nat.mul (nat_lit 8) (spT T a))) xp)

@[expose] noncomputable def dg (c k : Nat) : Nat := fld(c, Nat.shiftLeft k (nat_lit 2), nat_lit 15)

@[expose] noncomputable def adjB (M j k : Nat) : Nat := fld(M, Nat.add (Nat.shiftLeft j (nat_lit 3)) k, nat_lit 1)

@[expose] noncomputable def adjC : Nat :=
  sum8 fun j => sum8 fun i =>
    nIf(cart j i == -1, Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft j (nat_lit 3)) i), nat_lit 0)

@[expose] noncomputable def rtF (T M a : Nat) : Bool :=
  (fun c => all8 fun i => bAnd(Nat.beq (dgT T a i) (dg c i), bAnd(Nat.ble (pT T a i) (nat_lit 4),
      Nat.beq (Nat.add (Nat.add (pT T a i) (nat_lit 16)) (sum8 fun k => Nat.mul (adjB M i k) (dgT T a k)))
        (Nat.add (Nat.add (Nat.mul (nat_lit 2) (dgT T a i))
          (Nat.mul (nat_lit 8) (sum8 fun k => adjB M i k))) (nat_lit 2)))))
    (nthN (rootCodes ()) a)

@[expose] noncomputable def rtOK (T M : Nat) : Bool := allBelow (nat_lit 240) (nat_lit 4) (rtF T M)

@[expose] noncomputable def tabPF (T P j : Nat) : Bool :=
  allBelow (nat_lit 240) (nat_lit 4) fun a =>
    (fun b => bAnd(Nat.blt b (nat_lit 240), all8 fun k => bIf(Nat.beq k j,
        Nat.beq (Nat.add (dgT T b j) (pT T a j)) (Nat.add (dgT T a j) (nat_lit 2)),
        Nat.beq (dgT T b k) (dgT T a k))))
      (byteAt P (Nat.add (Nat.mul (nat_lit 240) j) a))

@[expose] noncomputable def tabNOK (T N : Nat) : Bool :=
  allBelow (nat_lit 240) (nat_lit 4) fun a =>
    (fun b => bAnd(Nat.blt b (nat_lit 240),
      all8 fun k => Nat.beq (Nat.add (dgT T b k) (dgT T a k)) (nat_lit 16)))
      (byteAt N a)

@[expose] noncomputable def tabDRow (T D a : Nat) : Bool :=
  allBelow (nat_lit 240) (nat_lit 4) fun b =>
    bIf(ipIs T a b (nat_lit 0) (nat_lit 1),
      (fun e => bAnd(Nat.blt e (nat_lit 240),
        all8 fun k => Nat.beq (Nat.add (dgT T e k) (nat_lit 8)) (Nat.add (dgT T a k) (dgT T b k))))
        (byteAt D (Nat.add (Nat.mul (nat_lit 240) a) b)), true)

@[expose] noncomputable def tabDF (T D k : Nat) : Bool :=
  allBelow (nat_lit 30) (nat_lit 1) fun t => tabDRow T D (Nat.add (Nat.mul (nat_lit 30) k) t)

@[expose] noncomputable def tabOK (T P N D M : Nat) : Bool :=
  rtOK T M && Nat.beq M adjC && allBelow 8 1 (tabPF T P) && tabNOK T N && allBelow 8 1 (tabDF T D)

@[expose] noncomputable def setK (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a ih => nIf(f a, Nat.lor ih (Nat.shiftLeft (nat_lit 1) a), ih)) (nat_lit 240)

@[expose] noncomputable def ones240 : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 240)) (nat_lit 1)

@[expose] noncomputable def selT (T : Nat) : Nat :=
  sum8 fun n => Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun v ih => Nat.add
    (Nat.shiftLeft (setK fun a => Nat.beq (pT T a n) v)
      (Nat.mul (nat_lit 240) (Nat.add (Nat.mul (nat_lit 5) n) v))) ih) (nat_lit 5)

@[expose] noncomputable def selK (S n v : Nat) : Nat :=
  nIf(Nat.ble v (nat_lit 4), fld(S, Nat.mul (nat_lit 240) (Nat.add (Nat.mul (nat_lit 5) n) v), ones240),
    nat_lit 0)

@[expose] noncomputable def qRow (neg : Bool) (Qs : List Nat) (T M S b T1 T0 : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun Q _ ih n => bAnd(all8 fun n' => Nat.beq
        (segK (fld(Q, Nat.mul (nat_lit 1984) b,
          Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1984)) (nat_lit 1))) n')
        (nIf(Nat.ble n' n, ones240, Nat.land (nIf(Nat.beq (adjB M n n') (nat_lit 1), T1, T0))
          (nIf(neg, nIf(Nat.ble (pT T b n') (nat_lit 4), selK S n (Nat.sub (nat_lit 4) (pT T b n')),
            nat_lit 0), selK S n (pT T b n'))))), ih (Nat.succ n))) Qs (nat_lit 0)

@[expose] noncomputable def qF (neg : Bool) (Qs : List Nat) (T k : Nat) : Bool :=
  (fun M S => allBelow (nat_lit 30) (nat_lit 1) fun t =>
      (fun b => qRow neg Qs T M S b (setK fun a => ipIs T b a (nat_lit 0) (nat_lit 1))
        (setK fun a => ipIs T b a (nat_lit 0) (nat_lit 0)))
      (Nat.add (Nat.mul (nat_lit 30) k) t))
    adjC (selT T)

@[expose] noncomputable def lenK (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def qXOK (neg : Bool) (X T : Nat) : Bool :=
  all8 fun n' => Nat.beq (segK X n') (nIf(neg, setK fun a => Nat.beq (pT T a n') (nat_lit 2), ones240))

@[expose] noncomputable def qOK (sgn : Int) (Qs : List Nat) (X T : Nat) : Bool :=
  (sgn == 1 || sgn == -1) && Nat.beq (lenK Qs) 7 && qXOK (sgn == -1) X T &&
    allBelow 8 1 (qF (sgn == -1) Qs T)

@[expose] noncomputable def startCol (k i : Nat) : Vec :=
  Bool.rec (motive := fun _ => Vec) (y0Word.foldr sRefl (basisV i))
    (((frameData ()).getD k []).foldr rRefl (basisV i)) (Nat.blt k (nat_lit 9))

@[expose] noncomputable def startF (S : List Nat) (k : Nat) : Bool :=
  (fun x => bAnd(Nat.blt x (Nat.shiftLeft (nat_lit 1) (nat_lit 64)),
      all8 fun i => (fun c => bAnd(Nat.blt c (nat_lit 240),
        (rootsL ()).getD c [] == startCol k i)) (byteAt x i)))
    (nthN S k)

@[expose] noncomputable def startsOK (S : List Nat) : Bool := allBelow 10 1 (startF S)

@[expose] noncomputable def negK (N x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor (Nat.shiftLeft (byteAt N (byteAt x i)) (Nat.shiftLeft i (nat_lit 3))) acc)
    (nat_lit 8)

@[expose] noncomputable def walkK (P N D M : Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun j _ ih x => strictN (conjK P N D M j x) ih) w

@[expose] noncomputable def lt8K (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun j _ ih => bAnd(Nat.blt j (nat_lit 8), ih)) w

@[expose] noncomputable def zwOK (P N D M s : Nat) (w : List Nat) (t : Nat) : Bool :=
  bAnd(lt8K w, Nat.beq (walkK P N D M w (negK N s)) t)

theorem allBelow_of {m hi : Nat} {f : Nat → Bool} (h : ∀ i < m, f i = true) :
    allBelow m hi f = true := by
  unfold allBelow
  induction hi with
  | zero => rfl
  | succ b ih =>
    have hin : ∀ l, Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
        bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft b 6) l), ih2)) l
          = true := by
      intro l
      induction l with
      | zero => rfl
      | succ l ihl =>
        change Bool.rec (motive := fun _ => Bool) false _
          (Bool.rec (motive := fun _ => Bool) true _ (Nat.blt (Nat.add (Nat.shiftLeft b 6) l) m))
          = true
        cases hb : Nat.blt (Nat.add (Nat.shiftLeft b 6) l) m
        · exact ihl
        · rw [h _ (Nat.blt_eq.mp hb)]
          exact ihl
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true (fun h ih => bAnd(
        Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
          bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h 6) l), ih2)) 64, ih)) b)
      (Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
          bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft b 6) l), ih2)) 64) = true
    rw [hin 64]
    exact ih

end CFSG.KC.WE8K

end
