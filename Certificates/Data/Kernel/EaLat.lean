module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.EaLat

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def m256 : Nat :=
  115792089237316195423570985008687907853269984665640564039457584007913129639935

@[expose] noncomputable def bit (m i : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) i))

@[expose] noncomputable def fld (r o w : Nat) : Nat := Nat.land (Nat.shiftRight r o) w

@[expose] noncomputable def letN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def pairAt (M : Nat → Nat → Nat) (n : Nat) (V CM PR : Nat → Nat)
    (ncw : Nat → Nat → Nat → Bool) (vi ci pi i j : Nat) : Bool :=
  letB (V j) fun vj => letB (CM j) fun cj => letB (fld pi (Nat.mul (nat_lit 8) j) (nat_lit 255)) fun e =>
    andB (Nat.beq e (fld (PR j) (Nat.mul (nat_lit 8) i) (nat_lit 255)))
      (Bool.rec (motive := fun _ => Bool)
        (andB (notB (bit cj i)) (ncw vj vi e))
        (andB (bit cj i) (andB (Nat.blt e n)
          (letB (V e) fun ve => andB (Nat.beq (M vi vj) ve) (Nat.beq (M vj vi) ve))))
        (bit ci j))

@[expose] noncomputable def uniAt (M : Nat → Nat → Nat) (one n : Nat) (V CM PR : Nat → Nat)
    (ncw : Nat → Nat → Nat → Bool) (i : Nat) : Bool :=
  letB (V i) fun vi => letB (CM i) fun ci => letB (PR i) fun pi =>
    andB (andB (notB (Nat.beq vi one)) (andB (Nat.beq (M vi vi) one)
      (andB (bit ci i) (Nat.blt ci (Nat.shiftLeft (nat_lit 1) n)))))
      (andB (impB (Nat.blt (Nat.succ i) n) (Nat.blt vi (V (Nat.succ i))))
        (allN i fun j => pairAt M n V CM PR ncw vi ci pi i j))

@[expose] noncomputable def baseOK (n : Nat) (REC : Nat → Nat) : Bool :=
  letB (REC (nat_lit 0)) fun r =>
    andB (Nat.beq (fld r (nat_lit 0) (nat_lit 4294967295)) (nat_lit 0))
      (andB (Nat.beq (fld r (nat_lit 64) m256) (nat_lit 0))
        (andB (Nat.beq (fld r (nat_lit 320) m256) (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)))
          (Nat.beq (Nat.shiftRight r (nat_lit 576)) (nat_lit 0))))

@[expose] noncomputable def prodW (prk elp szp acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) acc
    (fun t ih => letN (fld prk (Nat.mul (nat_lit 8) (fld elp (Nat.mul (nat_lit 8) t) (nat_lit 255)))
        (nat_lit 255)) fun c =>
      Nat.lor ih (Nat.lor (Nat.shiftLeft c (Nat.mul (nat_lit 8) (Nat.add (Nat.succ szp) t)))
        (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 512) c)))) szp

@[expose] noncomputable def genAt (n : Nat) (REC CM PR : Nat → Nat) (f : Nat) : Bool :=
  letB (REC f) fun r => letB (fld r (nat_lit 0) (nat_lit 65535)) fun p =>
    letB (fld r (nat_lit 16) (nat_lit 255)) fun k => letB (fld r (nat_lit 24) (nat_lit 255)) fun sz =>
    letB (REC p) fun rp => letB (fld rp (nat_lit 24) (nat_lit 255)) fun szp =>
    letB (fld rp (nat_lit 64) m256) fun mkp => letB (fld rp (nat_lit 320) m256) fun ccp =>
    letB (Nat.shiftRight rp (nat_lit 576)) fun elp => letB (Nat.shiftRight r (nat_lit 576)) fun el =>
    andB (andB (Nat.blt p f) (andB (Nat.blt k n) (andB (Nat.blt sz (nat_lit 64))
      (andB (Nat.beq sz (Nat.succ (Nat.add szp szp)))
        (Nat.blt el (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) sz)))))))
      (andB (andB (notB (bit mkp k)) (andB (bit ccp k)
        (Nat.beq (fld r (nat_lit 320) m256) (Nat.land ccp (CM k)))))
        (Nat.beq (prodW (PR k) elp szp
            (Nat.lor (Nat.lor elp (Nat.shiftLeft k (Nat.mul (nat_lit 8) szp)))
              (Nat.shiftLeft (Nat.lor mkp (Nat.shiftLeft (nat_lit 1) k)) (nat_lit 512))))
          (Nat.lor el (Nat.shiftLeft (fld r (nat_lit 64) m256) (nat_lit 512)))))

@[expose] noncomputable def covW (NF : Nat) (REC : Nat → Nat) (mk sz ch nc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t ih => letN (fld ch (Nat.mul (nat_lit 16) t) (nat_lit 65535)) fun c =>
      letN (REC c) fun rc => letN (fld rc (nat_lit 64) m256) fun mc =>
        Nat.lor ih (Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) (nat_lit 256)) mc
          (andB (Nat.blt c NF) (andB (Nat.beq (Nat.land mk mc) mk)
            (Nat.beq (fld rc (nat_lit 24) (nat_lit 255)) (Nat.succ (Nat.add sz sz))))))) nc

@[expose] noncomputable def covAt (NF : Nat) (REC CH : Nat → Nat) (f : Nat) : Bool :=
  letB (REC f) fun r => letB (fld r (nat_lit 64) m256) fun mk =>
    letB (fld r (nat_lit 320) m256) fun cc => letB (Nat.sub cc (Nat.land cc mk)) fun I =>
    letB (covW NF REC mk (fld r (nat_lit 24) (nat_lit 255)) (CH f) (fld r (nat_lit 32) (nat_lit 255)))
      fun acc => andB (notB (bit acc (nat_lit 256))) (Nat.beq (Nat.land I acc) I)

end CFSG.KC.EaLat

end
