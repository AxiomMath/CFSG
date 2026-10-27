module

public import Certificates.Data.Kernel.Fi22Twist.Search
public import Certificates.Data.Kernel.E27Lie.Defs

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Ord CFSG.KC.Enum CFSG.KC.E27Lie

@[expose] noncomputable def qpE (r t : Nat) : Nat := fld(r, Nat.mul (nat_lit 16) t, nat_lit 65535)

@[expose] noncomputable def qpBit (m i : Nat) : Bool := Nat.beq (fld(m, i, nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def qpFull : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 729)) (nat_lit 1)

@[expose] noncomputable def qpMul (p R S : Nat) : Bool :=
  allBlk (nat_lit 0) (fun l => Nat.beq (qpE R (Nat.add (nat_lit 2) l))
    (ap p (qpE S (Nat.add (nat_lit 2) l)))) (nat_lit 6)

@[expose] noncomputable def qpVM (row : Nat) : Nat :=
  foldN (nat_lit 9) (fun t s => Nat.lor s (Nat.shiftLeft (nat_lit 1) (qpE row t))) (nat_lit 0)

@[expose] noncomputable def qpXC (K X : Nat → Nat) (x : Nat) : Bool :=
  strictB (X x) fun r => strictB (K x) fun kx =>
  bAnd(allBlk (nat_lit 0) (fun l => Nat.beq (qpE r (Nat.add (nat_lit 2) l)) (ap kx (bp l)))
      (nat_lit 6),
    bAnd(strictB (qpE r (nat_lit 0)) fun s => bAnd(Nat.blt s (nat_lit 729), qpMul kx (X s) r),
      sortC (fun i => fld(X i, nat_lit 32, nat_lit 79228162514264337593543950335))
        (fun q => qpE (X q) (nat_lit 1)) (nat_lit 729) x))

@[expose] noncomputable def qpOC (K M X : Nat → Nat) (b : Nat) : Bool :=
  bIf(Nat.beq b (nat_lit 0), true, bIf(qpBit (M (nat_lit 0)) b, true,
    strictB (X b) fun r => strictB (K b) fun kb =>
      notB (allBlk (nat_lit 0) (fun l => Nat.beq (ap kb (ap kb (qpE r (Nat.add (nat_lit 2) l))))
        (bp l)) (nat_lit 6))))

@[expose] noncomputable def qpCC (K M X V : Nat → Nat) (x : Nat) : Bool :=
  bIf(qpBit (M (nat_lit 0)) x,
    strictB (K x) fun kx => strictB (X x) fun r => strictB (M (Nat.succ x)) fun cx =>
    strictB (Nat.land (M (nat_lit 0)) (Nat.xor qpFull cx)) fun m =>
    bAnd(allN (nat_lit 729) (fun b => bIf(qpBit m b,
        strictB (X b) fun rb => strictB (K b) fun kb =>
          notB (allBlk (nat_lit 0) (fun l => Nat.beq (ap kx (qpE rb (Nat.add (nat_lit 2) l)))
            (ap kb (qpE r (Nat.add (nat_lit 2) l)))) (nat_lit 6)), true)),
      strictB (qpE r (nat_lit 8)) fun nv =>
      bAnd(allN nv (fun t => strictB (qpE r (Nat.add (nat_lit 9) t)) fun v =>
          bAnd(Nat.blt v (nat_lit 517), qpBit (qpVM (V v)) x)),
        Nat.beq (Nat.land cx (Nat.land
          (Nat.xor qpFull (foldN nv (fun t s => Nat.lor s (qpVM (V (qpE r (Nat.add (nat_lit 9) t)))))
            (nat_lit 0)))
          (Nat.xor qpFull (Nat.lor (nat_lit 1) (Nat.lor (Nat.shiftLeft (nat_lit 1) x)
            (Nat.shiftLeft (nat_lit 1) (qpE r (nat_lit 0)))))))) (nat_lit 0))),
    true)

@[expose] noncomputable def qpVC (K M X V : Nat → Nat) (r : Nat) : Bool :=
  strictB (V r) fun row => strictB (qpE row (nat_lit 3)) fun a => strictB (qpE row (nat_lit 1)) fun b =>
  bAnd(Nat.beq (qpE row (nat_lit 0)) (nat_lit 0),
  bAnd(allN (nat_lit 9) (fun t => Nat.blt (qpE row t) (nat_lit 729)),
  bAnd(qpBit (M (nat_lit 0)) a, bAnd(qpBit (M (nat_lit 0)) b,
  strictB (K a) fun ka => strictB (K b) fun kb =>
  bAnd(allN (nat_lit 9) (fun t => bIf(Nat.blt t (nat_lit 3),
      bIf(Nat.beq t (nat_lit 0), true,
        qpMul kb (X (qpE row t)) (X (qpE row (Nat.sub t (nat_lit 1))))),
      qpMul ka (X (qpE row t)) (X (qpE row (Nat.sub t (nat_lit 3)))))),
  bAnd(qpMul ka (X (nat_lit 0)) (X (qpE row (nat_lit 6))),
  bAnd(qpMul kb (X (nat_lit 0)) (X (qpE row (nat_lit 2))),
  bAnd(qpMul kb (X (qpE row (nat_lit 4))) (X a),
  strictB (qpVM row) fun vm => strictB (qpE row (nat_lit 9)) fun nr =>
  bAnd(allN nr (fun t => strictB (qpE row (Nat.add (nat_lit 10) t)) fun c =>
      bAnd(Nat.blt c (nat_lit 81),
        Nat.beq (Nat.land vm (Nat.xor qpFull (M (Nat.add (nat_lit 730) c)))) (nat_lit 0))),
    Nat.beq (Nat.land (Nat.land (M (Nat.succ a)) (M (Nat.succ b))) (Nat.land (Nat.xor qpFull vm)
      (Nat.xor qpFull (foldN nr (fun t s => Nat.lor s
        (M (Nat.add (nat_lit 730) (qpE row (Nat.add (nat_lit 10) t))))) (nat_lit 0)))))
      (nat_lit 0))))))))))

end CFSG.KC.Fi22Twist

end
