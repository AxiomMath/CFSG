module

public import Certificates.Data.Kernel.Fi22Twist.Conj

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Ord CFSG.KC.Enum CFSG.KC.E27Lie

@[expose] noncomputable def tmF (L : Nat → Nat → Nat) (pp pj : Nat → Nat) (f a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => b)
    (fun _ ih a => nIf(Nat.beq a (nat_lit 0), b, strictN (ih (pp a)) (L (pj a)))) f a

@[expose] noncomputable def cntR (f : Nat → Bool) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun y s => nIf(f y, Nat.succ s, s)) n

@[expose] noncomputable def q01M (X Y : Nat) : Nat :=
  pcomp (nat_lit 3510) (nat_lit 12) (nat_lit 4095) X Y

@[expose] noncomputable def q01P (T : Nat → Nat) (i : Nat) : Nat := qpE (T i) (nat_lit 0)

@[expose] noncomputable def q01J (T : Nat → Nat) (i : Nat) : Nat := qpE (T i) (nat_lit 1)

@[expose] noncomputable def q01S (T : Nat → Nat) (q : Nat) : Nat := qpE (T q) (nat_lit 2)

@[expose] noncomputable def q01L (T : Nat → Nat) (t i : Nat) : Nat :=
  qpE (T i) (Nat.add (nat_lit 5) t)

@[expose] noncomputable def q01T (T : Nat → Nat) (n a b : Nat) : Nat :=
  tmF (q01L T) (q01P T) (q01J T) n a b

@[expose] noncomputable def q01Cube (T : Nat → Nat) (n a : Nat) : Bool :=
  Nat.beq (q01T T n a (q01T T n a a)) (nat_lit 0)

@[expose] noncomputable def q01C (K T DF : Nat → Nat) (G j n i : Nat) : Bool :=
  strictB (T i) fun row =>
  bAnd(treeC q01M K (q01P T) (q01J T) (fun t => K (Nat.succ t))
      (pidn (nat_lit 3510) (nat_lit 12)) (nat_lit 3) i,
  bAnd(allN (nat_lit 3) (fun t => leftC q01M K (q01L T) (fun t => K (Nat.succ t)) n t i),
  bAnd(sortC K (q01S T) n i,
    bIf(Nat.beq (qpE row (nat_lit 3)) (nat_lit 1),
      strictB (qpE row (nat_lit 4)) fun e => bAnd(Nat.blt e (nat_lit 27),
        cjFull G (K i) (DF (Nat.add (Nat.mul (nat_lit 27) j) e))),
      bIf(q01Cube T n i,
        Nat.blt (cntR (fun y => bAnd(q01Cube T n y,
          Nat.beq (q01T T n i y) (q01T T n y i))) n) (nat_lit 27),
        true)))))

end CFSG.KC.Fi22Twist

end
