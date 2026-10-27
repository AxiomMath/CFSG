module

public import Certificates.Data.Kernel.U6.F2K

public section

namespace CFSG.KC.O8Coh

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.U6F2

@[expose] noncomputable def idK6 : Nat := nat_lit 34630287489

@[expose] noncomputable def blk (v s : Nat) : Nat := fget v s (nat_lit 36)

@[expose] noncomputable def outerK (u w : Nat) : Nat :=
  orN (nat_lit 6) fun a =>
    Nat.shiftLeft (nIf(bit u a, fget w (nat_lit 0) (nat_lit 6), nat_lit 0)) (Nat.mul (nat_lit 6) a)

@[expose] noncomputable def colK (P l : Nat) : Nat :=
  orN (nat_lit 6) fun j => nIf(bit P (Nat.add (Nat.mul (nat_lit 6) j) l), pw2 j, nat_lit 0)

@[expose] noncomputable def cobK (G : List Nat) (v : Nat) : Nat :=
  orN (nat_lit 6) fun s => Nat.shiftLeft
    (Nat.xor (mulF (nat_lit 6) (getLD (nat_lit 0) G s) (blk v (nat_lit 0)))
      (mulF (nat_lit 6) (blk v (nat_lit 0)) (getLD (nat_lit 0) G s))) (Nat.mul s (nat_lit 36))

@[expose] noncomputable def gamTailK (M v b : Nat) (r : Nat) : Nat :=
  Nat.xor (Nat.xor (msumK (nat_lit 6) (fget M b (nat_lit 6)) fun d => blk v d)
      (mulF (nat_lit 6) (trK (nat_lit 6) M) (mulF (nat_lit 6) (blk v b) M)))
    (Nat.xor (outerK r (fget M b (nat_lit 6))) (outerK (fget M b (nat_lit 6)) r))

@[expose] noncomputable def gamBlockK (G : List Nat) (v k : Nat) : Nat :=
  nIf(Nat.blt k (nat_lit 6), Nat.xor (blk v k) (trK (nat_lit 6) (blk v k)),
    nIf(Nat.blt k (nat_lit 12), Nat.land (blk v (Nat.sub k (nat_lit 6))) idK6,
      gamTailK (getLD (nat_lit 0) G (Nat.div (Nat.sub k (nat_lit 12)) (nat_lit 6))) v
        (Nat.mod (Nat.sub k (nat_lit 12)) (nat_lit 6))
        (fget (blk v (nat_lit 6)) (Nat.div (Nat.sub k (nat_lit 12)) (nat_lit 6)) (nat_lit 6))))

@[expose] noncomputable def gamK (G : List Nat) (v : Nat) : Nat :=
  orN (nat_lit 48) fun k => Nat.shiftLeft (gamBlockK G v k) (Nat.mul k (nat_lit 36))

@[expose] noncomputable def modBlockK (M v i l : Nat) : Nat :=
  Nat.xor (Nat.xor (mulF (nat_lit 6) (msumK (nat_lit 6) (colK M l) fun d => blk v d) M)
      (mulF (nat_lit 6) M (blk v l)))
    (nIf(bit (fget (blk v (nat_lit 6)) i (nat_lit 6)) l, M, nat_lit 0))

@[expose] noncomputable def modK (G : List Nat) (v : Nat) : Nat :=
  orN (nat_lit 36) fun k => Nat.shiftLeft
    (modBlockK (getLD (nat_lit 0) G (Nat.div k (nat_lit 6))) v (Nat.div k (nat_lit 6))
      (Nat.mod k (nat_lit 6)))
    (Nat.mul k (nat_lit 36))

@[expose] noncomputable def extK (G : List Nat) (n : Nat) (ws : List (List Nat)) (v : Nat) : Nat :=
  orN n fun k => Nat.shiftLeft (Nat.shiftRight (urPairK (nat_lit 6) G
    ((List.range (nat_lit 6)).map fun s => blk v s) (getLD [] ws k)) (nat_lit 36))
    (Nat.mul k (nat_lit 36))

@[expose] noncomputable def segK (n : Nat) (B Q : List Nat) (f : Nat → Nat) (E : List Nat) (i : Nat) :
    Bool :=
  idRowsSeg n B Q ((List.range' (36 * i) 36).map f) ((E.drop (36 * i)).take 36) (36 * i)

end CFSG.KC.O8Coh

end
