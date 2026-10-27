module

public import Certificates.Data.Kernel.TitsOctK

public section

namespace CFSG.KC.TitsDK

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK

@[expose] noncomputable def recR (lp A : Nat → Nat) (k : Nat) (isRoot : Nat → Bool)
    (L cnt LAY ORD PR LB PS : Nat) : Bool :=
  bAnd(allN cnt (fun i => strictB (fw (nat_lit 13) ORD i) (fun x => bAnd(Nat.blt x (nat_lit 4680),
    strictB (fw (nat_lit 4) LB i) (fun j => bIf(Nat.beq j (nat_lit 15), isRoot x,
      strictB (fw (nat_lit 12) PR i) (fun p => bAnd(Nat.blt p i, bAnd(Nat.blt j k,
        actV lp (gp (A j)) (fw (nat_lit 13) ORD p) x)))))))),
    allN (nat_lit 4680) (fun x => bIf(Nat.beq (layAt LAY x) L,
      strictB (fw (nat_lit 13) PS x) (fun q => bAnd(Nat.blt q cnt, Nat.beq (fw (nat_lit 13) ORD q) x)),
      true)))

@[expose] noncomputable def stabK (lp : Nat → Nat) (PL : Nat) (E : Nat → Nat) (n a b : Nat) : Bool :=
  bAnd(allN n (fun i => bAnd(actV lp (gp (E i)) a a, actV lp (gp (E i)) b b)),
    allN (degK a) (fun k => anyN n (fun i =>
      bAnd(actV lp (gp (E i)) (nbK lp PL a k) (nbK lp PL a k),
        anyN (degK a) (fun k' =>
          bIf(actV lp (gp (E i)) (nbK lp PL a k') (nbK lp PL a k'), false, true))))))

@[expose] noncomputable def transK (lp : Nat → Nat) (PL : Nat) (E : Nat → Nat) (n a w : Nat) :
    Bool :=
  allN (degK a) (fun k => anyN n (fun i => actV lp (gp (E i)) w (nbK lp PL a k)))

@[expose] noncomputable def exactK (lp : Nat → Nat) (PL e w b k0 : Nat) : Bool :=
  bAnd(actV lp (gp e) w w, bAnd(Nat.blt k0 (degK b),
    allN (degK b) (fun k => bIf(Nat.beq k k0, actV lp (gp e) (nbK lp PL b k) (nbK lp PL b k),
      bIf(actV lp (gp e) (nbK lp PL b k) (nbK lp PL b k), false, true)))))

@[expose] noncomputable def labK (lp : Nat → Nat) (PL a : Nat) (lab : Nat → Nat) : Bool :=
  bAnd(Nat.beq (degK a) (nat_lit 5),
  bAnd(allN (nat_lit 5) (fun i => allN i (fun j => bIf(Nat.beq (lab i) (lab j), false, true))),
  bAnd(allN (nat_lit 5) (fun i => anyN (nat_lit 5) (fun k => Nat.beq (lab i) (nbK lp PL a k))),
    allN (nat_lit 5) (fun k => anyN (nat_lit 5) (fun i => Nat.beq (lab i) (nbK lp PL a k))))))

@[expose] noncomputable def affK (lp A : Nat → Nat) (k : Nat) (lab : Nat → Nat) (AF : Nat) : Bool :=
  allN k (fun j => strictB (fw (nat_lit 3) AF (Nat.mul (nat_lit 2) j)) (fun al =>
    strictB (fw (nat_lit 3) AF (Nat.add (Nat.mul (nat_lit 2) j) (nat_lit 1))) (fun be =>
      bAnd(Nat.blt (nat_lit 0) al, bAnd(Nat.blt al (nat_lit 5), bAnd(Nat.blt be (nat_lit 5),
        allN (nat_lit 5) (fun i => actV lp (gp (A j)) (lab i)
          (lab (Nat.mod (Nat.add (Nat.mul al i) be) (nat_lit 5))))))))))

end CFSG.KC.TitsDK

end
