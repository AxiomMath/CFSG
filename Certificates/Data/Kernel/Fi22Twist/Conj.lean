module

public import Certificates.Data.Kernel.Fi22Twist.Pairs

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Ord CFSG.KC.Enum CFSG.KC.E27Lie

@[expose] noncomputable def cjFull (G X D : Nat) : Bool :=
  allN (nat_lit 3510) fun z => Nat.beq (ap G (ap X z)) (ap D (ap G z))

@[expose] noncomputable def cjI (row t : Nat) : Nat :=
  qpE row (Nat.add (nat_lit 4) (Nat.mul (nat_lit 2) t))

@[expose] noncomputable def cjK (row t : Nat) : Nat :=
  qpE row (Nat.add (nat_lit 5) (Nat.mul (nat_lit 2) t))

@[expose] noncomputable def cjMask (row n : Nat) : Nat :=
  foldN n (fun t s => Nat.lor s (Nat.shiftLeft (nat_lit 1) (cjI row t))) (nat_lit 0)

@[expose] noncomputable def cjRep (K X DF : Nat → Nat) (g j row t : Nat) : Bool :=
  strictB (cjI row t) fun i => strictB (cjK row t) fun k =>
  bIf(Nat.blt t (nat_lit 3),
    bAnd(Nat.blt k (nat_lit 27),
      cjFull g (K i) (DF (Nat.add (Nat.mul (nat_lit 27) j) k))),
    strictB (Nat.mod k (nat_lit 4)) fun a => strictB (Nat.div k (nat_lit 4)) fun u =>
    bAnd(Nat.blt a (nat_lit 3), bAnd(Nat.blt u t,
      qpMul (K (cjI row a)) (X i) (X (cjI row u)))))

@[expose] noncomputable def cjSub (K M X : Nat → Nat) (p s row t : Nat) : Bool :=
  strictB (cjI row t) fun i => strictB (cjK row t) fun k =>
  bAnd(Nat.blt k (nat_lit 729), bAnd(qpBit (M (Nat.add (nat_lit 730) p)) k,
    strictB (K k) fun kk => strictB (K s) fun ks => strictB (X s) fun xs => strictB (X i) fun xi =>
    allBlk (nat_lit 0) (fun l => Nat.beq (ap kk (qpE xs (Nat.add (nat_lit 2) l)))
      (ap ks (qpE xi (Nat.add (nat_lit 2) l)))) (nat_lit 6)))

@[expose] noncomputable def cjRC (K M X DF CG RC : Nat → Nat) (nG c : Nat) : Bool :=
  strictB (RC c) fun row => strictB (qpE row (nat_lit 3)) fun n =>
  strictB (qpE row (nat_lit 1)) fun r => strictB (qpE row (nat_lit 2)) fun j =>
  bAnd(allN n (fun t => Nat.blt (cjI row t) (nat_lit 729)),
  bAnd(Nat.beq (Nat.land (M (Nat.add (nat_lit 730) c)) (Nat.xor qpFull (cjMask row n)))
      (nat_lit 0),
    bIf(Nat.beq (qpE row (nat_lit 0)) (nat_lit 0),
      bAnd(Nat.blt r nG, bAnd(Nat.blt j (nat_lit 5),
        strictB (CG r) fun g => allN n (cjRep K X DF g j row))),
      bAnd(Nat.blt r (nat_lit 81), bAnd(Nat.blt j (nat_lit 729),
        bAnd(Nat.blt (qpE (RC r) (nat_lit 0)) (qpE row (nat_lit 0)),
          allN n (cjSub K M X r j row)))))))

end CFSG.KC.Fi22Twist

end
