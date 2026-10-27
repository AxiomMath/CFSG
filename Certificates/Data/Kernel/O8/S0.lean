module

public import Certificates.Data.Kernel.O8.Core

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M

@[expose] noncomputable def tget (MT i j : Nat) : Nat :=
  fget MT (Nat.add (Nat.mul (nat_lit 64) i) j) (nat_lit 6)

@[expose] noncomputable def distinctOK (L : Nat) : Bool :=
  allN (nat_lit 64) fun i => allN (nat_lit 64) fun j =>
    orB (Nat.beq i j) (notB (Nat.beq (mat L i) (mat L j)))

@[expose] noncomputable def rowMT (MT i : Nat) : Nat := fget MT i (nat_lit 384)

@[expose] noncomputable def colMT (MT y : Nat) : Nat :=
  orN (nat_lit 64) fun a => Nat.shiftLeft (tget MT a y) (Nat.mul (nat_lit 6) a)

@[expose] noncomputable def mtOK (L MT : Nat) : Bool :=
  allN (nat_lit 64) fun i => Nat.beq (nat_lit 1) (strictN (rowMT MT i) fun R =>
    nIf(allN (nat_lit 64) fun j => Nat.beq (mat L (fget R j (nat_lit 6))) (bmulK (mat L i) (mat L j)),
      nat_lit 1, nat_lit 0))

@[expose] noncomputable def s0OK (L MT U UI TR : Nat) : Bool :=
  andB (Nat.beq (mat L (nat_lit 0)) ID6)
  (andB (distinctOK L)
  (andB (allN (nat_lit 64) fun i => allN (nat_lit 64) fun j => orB (Nat.beq i j)
      (anyN (nat_lit 6) fun c => notB (Nat.beq (bvecK (mat L i) (pw2 c)) (bvecK (mat L j) (pw2 c)))))
  (andB (allN (nat_lit 6) fun k => Nat.beq (mat L (fget UI k (nat_lit 6))) (mat U k))
  (andB (allN (nat_lit 64) fun i => Nat.beq (nat_lit 1) (strictN (rowMT MT i) fun R =>
      nIf(anyN (nat_lit 64) fun j => Nat.beq (fget R j (nat_lit 6)) (nat_lit 0), nat_lit 1, nat_lit 0)))
  (andB (Nat.beq (nat_lit 1) (strictN (rowMT MT (nat_lit 0)) fun R =>
      nIf(allN (nat_lit 64) fun y => Nat.beq (fget R y (nat_lit 6)) y, nat_lit 1, nat_lit 0)))
    (allN (nat_lit 63) fun i0 => (fun i e => (fun k j => andB (Nat.blt j i) (andB (Nat.blt k (nat_lit 6))
        (Nat.beq (bmulK (mat U k) (mat L j)) (mat L i))))
      (Nat.land e (nat_lit 7)) (Nat.shiftRight e (nat_lit 3)))
      (Nat.succ i0) (fget TR (Nat.succ i0) (nat_lit 9))))))))

@[expose] noncomputable def commMask (R Cc : Nat) : Nat :=
  orN (nat_lit 64) fun a =>
    nIf(Nat.beq (fget Cc a (nat_lit 6)) (fget R a (nat_lit 6)), pw2 a, nat_lit 0)

@[expose] noncomputable def commK (CM m : Nat) : Bool := Nat.beq (Nat.land m (Nat.xor CM (maskN (nat_lit 64)))) (nat_lit 0)

@[expose] noncomputable def imgK (Cc m : Nat) : Nat :=
  orN (nat_lit 64) fun a => nIf(bit m a, pw2 (fget Cc a (nat_lit 6)), nat_lit 0)

@[expose] noncomputable def closeK (Cc m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun m => m)
    (fun _ ih m => strictN (Nat.lor m (imgK Cc m)) ih) (nat_lit 8) m

@[expose] noncomputable def fixAll (F m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (maskN (nat_lit 64))
    (fun a ih => strictN ih fun acc => nIf(bit m a, Nat.land acc (fget F a (nat_lit 64)), acc))
    (nat_lit 64)

@[expose] noncomputable def fixOK (L F : Nat) : Bool :=
  allN (nat_lit 64) fun a => allN (nat_lit 64) fun z =>
    Nat.beq (bitN (fget F a (nat_lit 64)) z) (nIf(Nat.beq (bvecK (mat L a) z) z, nat_lit 1, nat_lit 0))

@[expose] noncomputable def abelOK (L MT F AM n CI : Nat) : Bool :=
  andB (Nat.beq (fget AM (nat_lit 0) (nat_lit 64)) (nat_lit 1))
  (andB (fixOK L F)
  (andB (allN (nat_lit 64) fun y => Nat.beq (nat_lit 1) (strictN (rowMT MT y) fun R =>
      strictN (colMT MT y) fun Cc => strictN (commMask R Cc) fun CM =>
      strictN (fget CI y (Nat.mul (nat_lit 8) n)) fun CY =>
        nIf(allN n fun k => (fun m => orB (bit m y) (orB (notB (commK CM m))
            ((fun c => andB (Nat.blt c n) (Nat.beq (closeK Cc m) (fget AM c (nat_lit 64))))
              (fget CY k (nat_lit 8)))))
          (fget AM k (nat_lit 64)), nat_lit 1, nat_lit 0)))
    (allN n fun k => (fun m => Nat.ble (Nat.mul (popc (nat_lit 64) m) (popc (nat_lit 64) (fixAll F m)))
      (nat_lit 64)) (fget AM k (nat_lit 64)))))

end CFSG.KC.O8

end
