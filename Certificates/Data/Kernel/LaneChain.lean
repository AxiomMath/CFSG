module

public import CFSG.Certificates.Kernel.Orders.Cert

public section

namespace CFSG.KC.LaneChain

open CFSG.KC.Ord CFSG.KC.Loop

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def getN (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l

@[expose] noncomputable def getR (l : List Nat) (n r : Nat) : Nat :=
  getN l (Nat.sub (Nat.sub n (nat_lit 1)) r)

@[expose] noncomputable def getL (l : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) l

@[expose] noncomputable def allLt (w : List Nat) (n : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih => andB (Nat.blt r n) ih) w

@[expose] noncomputable def wfold (mul : Nat → Nat → Nat) (M : List Nat) (n : Nat)
    (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun r _ ih acc => strictN (mul acc (getR M n r)) ih) w

@[expose] noncomputable def wprod (mul : Nat → Nat → Nat) (M : List Nat) (n : Nat)
    (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun r rs _ => wfold mul M n rs (getR M n r)) w

@[expose] noncomputable def regsK (mul : Nat → Nat → Nat) (k : List Nat → Nat → Bool)
    (W : List (List Nat)) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool) (fun M n => k M n)
    (fun w _ ih M n => andB (andB (notB (Nat.beq (lenL w) (nat_lit 0))) (allLt w n))
      (strictB (wprod mul M n w) (fun x => ih (List.cons x M) (Nat.succ n)))) W

@[expose] noncomputable def colDat (S : Nat) (v : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => Nat.add a (Nat.shiftLeft ih S)) v

@[expose] noncomputable def basesK (vld : Nat → Bool) (S : Nat) (k : List Nat → Bool)
    (Bs : List (List Nat)) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun Xs => k Xs)
    (fun b _ ih Xs => strictB (colDat S b)
      (fun x => andB (vld x) (ih (List.append Xs (List.cons x List.nil))))) Bs

@[expose] noncomputable def notIn (x : Nat) (V : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => andB (notB (Nat.beq x y)) ih) V

@[expose] noncomputable def memN (r : Nat) (G : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => orB (Nat.beq r y) ih) G

@[expose] noncomputable def gensK (mul : Nat → Nat → Nat) (M Xs G : List Nat) (nreg k : Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (andB (Nat.blt r nreg)
      (Nat.rec (motive := fun _ => Bool) true
        (fun j ih2 => andB ih2 (Nat.beq (mul (getR M nreg r) (getN Xs j)) (getN Xs j))) k)) ih) G

@[expose] noncomputable def treeK (mul : Nat → Nat → Nat) (M : List Nat) (nreg : Nat)
    (G : List Nat) (k : Nat → Bool) (T : List Nat) : Nat → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → List Nat → Nat → Bool)
    (fun pend _ n => andB (Nat.beq pend (nat_lit 0)) (k n))
    (fun c _ ih pend V n => Nat.rec (motive := fun _ => Bool)
      (andB (Nat.blt c n) (ih (Nat.succ c) V n))
      (fun p _ => andB (memN c G) (strictB (mul (getR M nreg c) (getR V n p))
        (fun v => andB (notIn v V) (ih (nat_lit 0) (List.cons v V) (Nat.succ n)))))
      pend) T

@[expose] noncomputable def levelsK (mul : Nat → Nat → Nat) (M : List Nat) (nreg : Nat)
    (Xs : List Nat) (tot : Nat) (Ts : List (List Nat)) (Gs : List (List Nat)) :
    Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ acc => Nat.beq acc tot)
    (fun G _ ih k acc => andB (andB (Nat.blt k (lenL Xs)) (gensK mul M Xs G nreg k))
      (treeK mul M nreg G (fun n => ih (Nat.succ k) (Nat.mul acc n)) (getL Ts k) (nat_lit 0)
        (List.cons (getN Xs k) List.nil) (nat_lit 1))) Gs

@[expose] noncomputable def chainOK (mul : Nat → Nat → Nat) (vld : Nat → Bool) (S : Nat)
    (W Bs Gs Ts : List (List Nat)) (M₀ : List Nat) (tot : Nat) : Bool :=
  regsK mul (fun M nreg => basesK vld S
      (fun Xs => levelsK mul M nreg Xs tot Ts Gs (nat_lit 0) (nat_lit 1)) Bs List.nil)
    W M₀ (lenL M₀)

end CFSG.KC.LaneChain

end
