module

public import Certificates.Data.Kernel.MonsterB.U6Orb

public section

namespace CFSG.KC.Orb14

open CFSG.KLie.CT CFSG.KC.U6Orb

@[expose] noncomputable def bindL (L : List Nat) (X w n b : Nat) : Bool :=
  andB (Nat.beq (packL w L) X) (andB (Nat.beq (lenL L) n) (boundL b L))

@[expose] noncomputable def bindP (P : List (Array Nat)) (X n w m b : Nat) : Bool :=
  andB (Nat.beq (packP n w P) X) (andB (Nat.beq (lenL P) m) (shapeL n b P))

@[expose] noncomputable def incOK (A m w N : Nat) : Bool :=
  allN m fun t => Nat.blt (fget A t w) (nIf(Nat.beq (Nat.succ t) m, N, fget A (Nat.succ t) w))

@[expose] noncomputable def maskF (A m w : Nat) : Nat := orN m fun t => pw2 (fget A t w)

@[expose] noncomputable def maskB (n : Nat) (f : Nat → Bool) : Nat :=
  orN n fun x => nIf(f x, pw2 x, nat_lit 0)

@[expose] noncomputable def xorB (a b : Bool) : Bool := Bool.rec b (notB b) a

@[expose] noncomputable def sel (c : Bool) (x : Nat) : Nat := nIf(c, x, nat_lit 0)

@[expose] noncomputable def dsw (s m x : Nat) : Nat :=
  Nat.xor (Nat.xor x (Nat.land (Nat.xor (Nat.shiftRight x s) x) m))
    (Nat.shiftLeft (Nat.land (Nat.xor (Nat.shiftRight x s) x) m) s)

@[expose] noncomputable def stg (W : Nat) : List (Nat × Nat) :=
  [(512, fget W 0 1024), (256, fget W 1 1024), (128, fget W 2 1024), (64, fget W 3 1024),
    (32, fget W 4 1024), (16, fget W 5 1024), (8, fget W 6 1024), (4, fget W 7 1024),
    (2, fget W 8 1024), (1, fget W 9 1024), (2, fget W 10 1024), (4, fget W 11 1024),
    (8, fget W 12 1024), (16, fget W 13 1024), (32, fget W 14 1024), (64, fget W 15 1024),
    (128, fget W 16 1024), (256, fget W 17 1024), (512, fget W 18 1024)]

@[expose] noncomputable def netK (W x : Nat) : Nat :=
  (fun M => dsw 512 (M 18) (dsw 256 (M 17) (dsw 128 (M 16) (dsw 64 (M 15) (dsw 32 (M 14)
    (dsw 16 (M 13) (dsw 8 (M 12) (dsw 4 (M 11) (dsw 2 (M 10) (dsw 1 (M 9) (dsw 2 (M 8)
    (dsw 4 (M 7) (dsw 8 (M 6) (dsw 16 (M 5) (dsw 32 (M 4) (dsw 64 (M 3) (dsw 128 (M 2)
    (dsw 256 (M 1) (dsw 512 (M 0) x))))))))))))))))))) (fun t => fget W t (nat_lit 1024))

@[expose] noncomputable def netR (W x : Nat) : Nat :=
  (fun M => dsw 512 (M 0) (dsw 256 (M 1) (dsw 128 (M 2) (dsw 64 (M 3) (dsw 32 (M 4)
    (dsw 16 (M 5) (dsw 8 (M 6) (dsw 4 (M 7) (dsw 2 (M 8) (dsw 1 (M 9) (dsw 2 (M 10)
    (dsw 4 (M 11) (dsw 8 (M 12) (dsw 16 (M 13) (dsw 32 (M 14) (dsw 64 (M 15) (dsw 128 (M 16)
    (dsw 256 (M 17) (dsw 512 (M 18) x))))))))))))))))))) (fun t => fget W t (nat_lit 1024))

@[expose] noncomputable def netOK (W : Nat) : Bool :=
  allL (fun p => andB (Nat.blt 0 p.1) (andB (Nat.beq (Nat.land p.2 (Nat.shiftLeft p.2 p.1)) 0)
    (Nat.blt p.2 (pw2 (Nat.sub 1024 p.1))))) (stg W)

@[expose] noncomputable def nw (NW k : Nat) : Nat := fget NW k (nat_lit 19456)

@[expose] noncomputable def edgeOK (B NW Ed o n ng N : Nat) : Bool :=
  allN n fun l => allN ng fun k => Nat.beq (netK (nw NW k) (fget B (Nat.add o l) N))
    (fget B (fget Ed (Nat.add (Nat.mul (Nat.add o l) ng) k) (nat_lit 11)) N)

@[expose] noncomputable def idPl (b : Nat) : Nat := maskB 1024 fun q => bit q b

@[expose] noncomputable def permPl (P N k b : Nat) : Nat :=
  maskB 1024 fun x => bit (nIf(Nat.blt x N, permTab N 10 P x k, x)) b

@[expose] noncomputable def tieN (NW P N : Nat) : Bool :=
  allN 17 fun k => andB (netOK (nw NW k))
    (allN 10 fun b => Nat.beq (netK (nw NW k) (permPl P N k b)) (idPl b))

@[expose] noncomputable def cb (x t s : Nat) : Bool := bit x (Nat.add (Nat.add t t) s)

@[expose] noncomputable def xp (X c : Nat) : Nat := fget X c (nat_lit 693)

@[expose] noncomputable def frPl (X : Nat) (f : Bool) (t s : Nat) : Nat :=
  nIf(Nat.beq s 0, nIf(f, Nat.xor (xp X (Nat.add t t)) (xp X (Nat.succ (Nat.add t t))),
    xp X (Nat.add t t)), xp X (Nat.succ (Nat.add t t)))

@[expose] noncomputable def combPl (n : Nat) (A : Nat → Nat → Nat) (m : Nat → Nat) (t s : Nat) :
    Nat :=
  xorK n fun r => nIf(Nat.beq s 0,
    Nat.xor (sel (cb (m r) t 0) (A r 0)) (sel (cb (m r) t 1) (A r 1)),
    Nat.xor (sel (cb (m r) t 1) (A r 0)) (sel (xorB (cb (m r) t 0) (cb (m r) t 1)) (A r 1)))

@[expose] noncomputable def imPl (X M F k t s : Nat) : Nat :=
  combPl 6 (frPl X (bit F k)) (fun r => permTab 6 12 M r k) t s

@[expose] noncomputable def firstPl (W : Nat → Nat → Nat) (t : Nat) : Nat :=
  Nat.land (Nat.lor (W t 0) (W t 1))
    (Nat.xor (maskN 693) (orN t fun s => Nat.lor (W s 0) (W s 1)))

@[expose] noncomputable def leadPl (W : Nat → Nat → Nat) (s : Nat) : Nat :=
  xorK 6 fun t => Nat.land (firstPl W t) (W t s)

@[expose] noncomputable def normPl (W : Nat → Nat → Nat) (t s : Nat) : Nat :=
  (fun l0 l1 => nIf(Nat.beq s 0, Nat.xor (Nat.land l0 (W t 0)) (Nat.land l1 (W t 1)),
    Nat.xor (Nat.land l1 (W t 0)) (Nat.land (Nat.xor l0 l1) (W t 1))))
    (Nat.xor (leadPl W 0) (leadPl W 1)) (leadPl W 1)

@[expose] noncomputable def singU (X M F k t s : Nat) : Nat := normPl (imPl X M F k) t s

@[expose] noncomputable def tieS (NW X M F : Nat) : Bool :=
  allN 17 fun k => andB (netOK (nw NW k)) (allN 6 fun t => allN 2 fun s =>
    Nat.beq (netK (nw NW k) (singU X M F k t s)) (xp X (Nat.add (Nat.add t t) s)))

@[expose] noncomputable def xpOK (X S : Nat) : Bool :=
  allN 12 fun c => Nat.beq (xp X c) (maskB 693 fun i => bit (fget S i 12) c)

@[expose] noncomputable def pivK (r : Nat) : Nat :=
  nIf(Nat.blt 0 (fget r 0 2), 0, nIf(Nat.blt 0 (fget r 1 2), 1, nIf(Nat.blt 0 (fget r 2 2), 2,
    nIf(Nat.blt 0 (fget r 3 2), 3, nIf(Nat.blt 0 (fget r 4 2), 4, nIf(Nat.blt 0 (fget r 5 2), 5,
    0))))))

@[expose] noncomputable def planeD (X : Nat) (R : Nat → Nat) : Nat :=
  orN 6 fun t => orN 2 fun s => Nat.xor
    (combPl 3 (fun b s' => xp X (Nat.add (Nat.add (pivK (R b)) (pivK (R b))) s')) R t s)
    (xp X (Nat.add (Nat.add t t) s))

@[expose] noncomputable def rowP (PL p b : Nat) : Nat := permTab 3 12 PL b p

@[expose] noncomputable def incidOK (X PL PU MO MP o n : Nat) : Bool :=
  allN n fun l => (fun p => (fun A => andB (incOK A 21 10 693)
    (andB (Nat.beq (Nat.xor (maskN 693) (planeD X (rowP PL p))) (maskF A 21 10))
      (Nat.beq (sumN 21 fun t => nIf(bit MO (fget A t 10), 1, 0)) (nIf(bit MP p, 0, 6)))))
    (fget PU p 210)) (Nat.add o l)

@[expose] noncomputable def coverStep (NW R : Nat) : Nat :=
  Nat.lor R (Nat.lor (netR (nw NW 1) (netK (nw NW 2) R)) (Nat.lor (netK (nw NW 4) R)
    (Nat.lor (netK (nw NW 6) R) (Nat.lor (netK (nw NW 7) R)
    (Nat.lor (netR (nw NW 12) (netK (nw NW 14) R)) (Nat.lor (netK (nw NW 16) R)
      (netR (nw NW 5) (netK (nw NW 3) (netK (nw NW 2) (netK (nw NW 0) R))))))))))

@[expose] noncomputable def cover (NW R L : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) R (fun _ R' => coverStep NW R') L

end CFSG.KC.Orb14

end
