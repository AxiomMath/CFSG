module

public import Certificates.Data.Kernel.Co2InvS

public section

namespace CFSG.KC.Co2Syl

open CFSG.KC.Loop CFSG.KC.Co2InvS

@[expose] noncomputable def edgeT (CF : Nat → Nat) (N m X g t : Nat) : Bool :=
  implK (notK (Nat.blt t m)) (edgeK CF N X g t)

@[expose] noncomputable def recT (CF G : Nat → Nat) (N k : Nat) : Bool :=
  letB (recAt CF k) fun r => letB (elemOf r) fun X => letB (mOf r) fun m =>
    andK (edgeT CF N m X (G (nat_lit 0)) (tOf r (nat_lit 0))) (
    andK (edgeT CF N m X (G (nat_lit 1)) (tOf r (nat_lit 1))) (
    andK (edgeT CF N m X (G (nat_lit 2)) (tOf r (nat_lit 2))) (
    andK (edgeT CF N m X (G (nat_lit 3)) (tOf r (nat_lit 3))) (
    andK (edgeT CF N m X (G (nat_lit 4)) (tOf r (nat_lit 4))) (
    andK (Nat.blt k m) (
    andK (Nat.beq (rowK m (tOf r (nat_lit 0)) (tOf r (nat_lit 1)) (tOf r (nat_lit 2))
        (tOf r (nat_lit 3)) (tOf r (nat_lit 4))) (nextM CF N k))
      (sortK CF N k (sOf r))))))))

@[expose] noncomputable def sqC (A B X : Nat) : Nat :=
  strictN (mulV X X) fun S =>
    Nat.add (selN (Nat.beq S A) (nat_lit 1) (nat_lit 0)) (selN (Nat.beq S B) (nat_lit 256) (nat_lit 0))

@[expose] noncomputable def sqK (CF : Nat → Nat) (A B N k : Nat) : Nat :=
  selN (Nat.blt k N) (sqC A B (elemAt CF k)) (nat_lit 0)

@[expose] noncomputable def blkRecs (CF G : Nat → Nat) (N b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andK (implK (Nat.blt (Nat.add (Nat.mul (nat_lit 64) b) i) N)
      (recT CF G N (Nat.add (Nat.mul (nat_lit 64) b) i))) acc) (nat_lit 64)

@[expose] noncomputable def blkSq (CF : Nat → Nat) (A B N b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (sqK CF A B N (Nat.add (Nat.mul (nat_lit 64) b) i))) (nat_lit 64)

@[expose] noncomputable def blkT (CF G : Nat → Nat) (A B : Nat) (CNT : Nat → Nat) (N b : Nat) :
    Bool :=
  andK (blkRecs CF G N b) (Nat.beq (blkSq CF A B N b) (cntAt CNT b))

@[expose] noncomputable def LOWM : Nat :=
  nat_lit 49947970850790916861576517211478066636458382238924778326972402748821361155519423233857073031965891722943047920745032561820306982588046674348736513

@[expose] noncomputable def triK (U : Nat) : Bool := Nat.beq (Nat.land U LOWM) IDP

@[expose] noncomputable def utK (B Bi : Nat) (G : Nat → Nat) : Bool :=
  andK (Nat.beq (mulV B Bi) IDP) (
  andK (triK (mulV (mulV Bi (G (nat_lit 0))) B)) (
  andK (triK (mulV (mulV Bi (G (nat_lit 1))) B)) (
  andK (triK (mulV (mulV Bi (G (nat_lit 2))) B)) (
  andK (triK (mulV (mulV Bi (G (nat_lit 3))) B))
    (triK (mulV (mulV Bi (G (nat_lit 4))) B))))))

@[expose] noncomputable def labAt (LD : Nat → Nat) (k : Nat) : Nat :=
  fld(LD (Nat.shiftRight k (nat_lit 6)), Nat.mul (Nat.land k (nat_lit 63)) (nat_lit 112),
    nat_lit 5192296858534827628530496329220095)

@[expose] noncomputable def labOf (q : Nat) : Nat := fld(q, nat_lit 0, nat_lit 65535)

@[expose] noncomputable def cjOf (q j : Nat) : Nat :=
  fld(q, Nat.mul (nat_lit 16) (Nat.succ j), nat_lit 65535)

@[expose] noncomputable def dOf (q : Nat) : Nat := fld(q, nat_lit 96, nat_lit 65535)

@[expose] noncomputable def labK0 (LD : Nat → Nat) (k : Nat) : Nat := labOf (labAt LD k)

@[expose] noncomputable def cjK (CF LD : Nat → Nat) (N X l g c : Nat) : Bool :=
  andK (Nat.blt c N) (andK (Nat.beq (mulV (elemAt CF c) g) (mulV g X)) (Nat.beq (labK0 LD c) l))

@[expose] noncomputable def dK (CF LD : Nat → Nat) (N l d Z : Nat) : Bool :=
  bIf(Nat.blt d N, andK (Nat.beq (elemAt CF d) Z) (notK (Nat.beq (labK0 LD d) l)), notK (involK Z))

@[expose] noncomputable def labK (CF G LD : Nat → Nat) (R N k : Nat) : Bool :=
  letB (elemAt CF k) fun X => implK (involK X) (letB (labAt LD k) fun q => letB (labOf q) fun l =>
    andK (cjK CF LD N X l (G (nat_lit 0)) (cjOf q (nat_lit 0))) (
    andK (cjK CF LD N X l (G (nat_lit 1)) (cjOf q (nat_lit 1))) (
    andK (cjK CF LD N X l (G (nat_lit 2)) (cjOf q (nat_lit 2))) (
    andK (cjK CF LD N X l (G (nat_lit 3)) (cjOf q (nat_lit 3))) (
    andK (cjK CF LD N X l (G (nat_lit 4)) (cjOf q (nat_lit 4)))
      (dK CF LD N l (dOf q) (mulV X R)))))))

@[expose] noncomputable def witK (CF : Nat → Nat) (R N a b : Nat) : Bool :=
  andK (Nat.blt a N) (andK (Nat.blt b N) (andK (involK (elemAt CF a))
    (Nat.beq (mulV (elemAt CF b) (elemAt CF a)) (mulV (mulV (elemAt CF a) R) (elemAt CF b)))))

@[expose] noncomputable def memK (CF : Nat → Nat) (N R k : Nat) : Bool :=
  andK (Nat.blt k N) (Nat.beq (elemAt CF k) R)

@[expose] noncomputable def commK (X Y : Nat) : Bool := Nat.beq (mulV X Y) (mulV Y X)

end CFSG.KC.Co2Syl

end
