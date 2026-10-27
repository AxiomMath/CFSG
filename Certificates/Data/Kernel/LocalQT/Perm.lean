module

public import CFSG.Certificates.Kernel.Orders.Mat

public section

namespace CFSG.KC.LQT.P

open CFSG.KC.Ord

@[expose] noncomputable def img (s i : Nat) : Nat :=
  Nat.land (Nat.shiftRight s (Nat.mul (nat_lit 5) i)) (nat_lit 31)

@[expose] noncomputable def ofFn (n : Nat) (g : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.shiftLeft (g i) (Nat.mul (nat_lit 5) i))) n

@[expose] noncomputable def mul (n s t : Nat) : Nat := ofFn n fun i => img s (img t i)

@[expose] noncomputable def inv (n s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.shiftLeft i (Nat.mul (nat_lit 5) (img s i)))) n

@[expose] noncomputable def one (n : Nat) : Nat := ofFn n fun i => i

@[expose] noncomputable def pow (n s k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (one n) (fun _ acc => mul n acc s) k

@[expose] noncomputable def swap (n a b : Nat) : Nat :=
  ofFn n fun i => Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) i a (Nat.beq i b)) b (Nat.beq i a)

@[expose] noncomputable def fix (n s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (Nat.beq (img s i) i))) n

@[expose] noncomputable def invs (n s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.add acc (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc2 => Nat.add acc2 (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
        (Nat.blt (img s j) (img s i)))) j)) n

@[expose] noncomputable def even (n s : Nat) : Bool := Nat.beq (Nat.mod (invs n s) (nat_lit 2)) (nat_lit 0)

@[expose] noncomputable def impB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true b a

@[expose] noncomputable def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def dfs (n : Nat) (comb : Bool → Bool → Bool) (unit : Bool)
    (f : Nat → Bool) (d : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun _ _ acc => f acc)
    (fun _ ih pos mask acc =>
      Nat.rec (motive := fun _ => Bool) unit
        (fun v rest => comb
          (Bool.rec (motive := fun _ => Bool)
            (letB (Nat.add acc (Nat.shiftLeft v (Nat.mul (nat_lit 5) pos))) fun a =>
              letB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) v)) fun m =>
                ih (Nat.succ pos) m a)
            unit (Nat.blt (nat_lit 0) (Nat.land mask (Nat.shiftLeft (nat_lit 1) v))))
          rest) n) d

@[expose] noncomputable def allP (n : Nat) (f : Nat → Bool) : Bool :=
  dfs n andB true f n (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def anyP (n : Nat) (f : Nat → Bool) : Bool :=
  dfs n orB false f n (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def cntP (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun _ _ acc => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (f acc))
    (fun _ ih pos mask acc =>
      Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun v rest => Nat.add
          (Bool.rec (motive := fun _ => Nat)
            (ih (Nat.succ pos) (Nat.lor mask (Nat.shiftLeft (nat_lit 1) v))
              (Nat.add acc (Nat.shiftLeft v (Nat.mul (nat_lit 5) pos))))
            (nat_lit 0) (Nat.blt (nat_lit 0) (Nat.land mask (Nat.shiftLeft (nat_lit 1) v))))
          rest) n) n (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def cOK (s si acc pos v : Nat) : Bool :=
  andB (impB (Nat.blt (img s pos) pos) (Nat.beq (img acc (img s pos)) (img s v)))
    (impB (Nat.blt (img si pos) pos) (Nat.beq v (img s (img acc (img si pos)))))

@[expose] noncomputable def dfsC (n s si : Nat) (comb : Bool → Bool → Bool) (unit : Bool)
    (f : Nat → Bool) (d : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun _ _ acc => f acc)
    (fun _ ih pos mask acc =>
      Nat.rec (motive := fun _ => Bool) unit
        (fun v rest => comb
          (Bool.rec (motive := fun _ => Bool)
            (Bool.rec (motive := fun _ => Bool) unit
              (letB (Nat.add acc (Nat.shiftLeft v (Nat.mul (nat_lit 5) pos))) fun a =>
                letB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) v)) fun m =>
                  ih (Nat.succ pos) m a)
              (cOK s si acc pos v))
            unit (Nat.blt (nat_lit 0) (Nat.land mask (Nat.shiftLeft (nat_lit 1) v))))
          rest) n) d

@[expose] noncomputable def allC (n s : Nat) (f : Nat → Bool) : Bool :=
  letB (inv n s) fun si => dfsC n s si andB true f n (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def anyC (n s : Nat) (f : Nat → Bool) : Bool :=
  letB (inv n s) fun si => dfsC n s si orB false f n (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def allN (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) m

@[expose] noncomputable def anyN (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => orB (f i) ih) m

@[expose] noncomputable def allL (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def anyL (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (f x) ih) l

@[expose] noncomputable def comm (n x y : Nat) : Bool := Nat.beq (mul n x y) (mul n y x)

@[expose] noncomputable def conj (n g x : Nat) : Nat := mul n (mul n g x) (inv n g)

@[expose] noncomputable def permK (n s : Nat) : Bool :=
  andB (Nat.beq s (ofFn n (img s))) (andB (allN n fun i => Nat.blt (img s i) n)
    (Nat.beq (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (img s i))) n)
      (Nat.sub (Nat.shiftLeft 1 n) 1)))

end CFSG.KC.LQT.P

end
