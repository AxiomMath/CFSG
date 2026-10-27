module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def ent (R : Nat → Nat) (k l : Nat) : Nat := pg (nat_lit 12) (mask 12) (R k) l

@[expose] noncomputable def mk (m a b : Nat) : Nat :=
  Nat.add (Nat.add (Nat.mul (nat_lit 16) m) (Nat.mul (nat_lit 4) (Nat.mod a (nat_lit 4))))
    (Nat.mod b (nat_lit 4))

@[expose] noncomputable def mulC (T : Nat → Nat) (x y : Nat) : Nat :=
  strictN (ent T (Nat.div x (nat_lit 16)) (Nat.div y (nat_lit 16))) fun v =>
    mk (Nat.div v (nat_lit 48))
      (Nat.add (Nat.add (Nat.mod (Nat.div x (nat_lit 4)) (nat_lit 4))
        (Nat.mod (Nat.div y (nat_lit 4)) (nat_lit 4))) (Nat.div (Nat.mod v (nat_lit 48)) (nat_lit 12)))
      (Nat.add (Nat.add (Nat.mod x (nat_lit 4)) (Nat.mod y (nat_lit 4)))
        (Nat.div (Nat.mod v (nat_lit 12)) (nat_lit 3)))

@[expose] noncomputable def betaRepC (A : Nat → Nat) (i x : Nat) : Nat :=
  strictN (ent A i (Nat.div x (nat_lit 16))) fun v =>
  strictN (ent A i (nat_lit 64)) fun p =>
  strictN (ent A i (nat_lit 65)) fun q =>
  strictN (Nat.mod (Nat.div x (nat_lit 4)) (nat_lit 4)) fun a =>
  strictN (Nat.mod x (nat_lit 4)) fun b =>
    mk (Nat.div v (nat_lit 48))
      (Nat.add (Nat.div (Nat.mod v (nat_lit 48)) (nat_lit 12))
        (Nat.add (Nat.mul a (Nat.div (Nat.mod p (nat_lit 48)) (nat_lit 12)))
          (Nat.mul b (Nat.div (Nat.mod q (nat_lit 48)) (nat_lit 12)))))
      (Nat.add (Nat.div (Nat.mod v (nat_lit 12)) (nat_lit 3))
        (Nat.add (Nat.mul a (Nat.div (Nat.mod p (nat_lit 12)) (nat_lit 3)))
          (Nat.mul b (Nat.div (Nat.mod q (nat_lit 12)) (nat_lit 3)))))

@[expose] noncomputable def firstC (p : Nat → Bool) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j ih => strictN ih fun r => nIf(Nat.blt r j, r, nIf(p j, j, Nat.succ j))) n

@[expose] noncomputable def invIdxC (T : Nat → Nat) (k : Nat) : Nat :=
  strictN (firstC (fun k' => Nat.beq (Nat.div (ent T k k') (nat_lit 48)) (nat_lit 0)) (nat_lit 64))
    fun r => nIf(Nat.blt r (nat_lit 64), r, nat_lit 0)

@[expose] noncomputable def invC (T : Nat → Nat) (x : Nat) : Nat :=
  strictN (Nat.div x (nat_lit 16)) fun k =>
  strictN (invIdxC T k) fun k' =>
  strictN (ent T k k') fun v =>
    mk k'
      (Nat.sub (Nat.sub (nat_lit 8) (Nat.div (Nat.mod v (nat_lit 48)) (nat_lit 12)))
        (Nat.mod (Nat.div x (nat_lit 4)) (nat_lit 4)))
      (Nat.sub (Nat.sub (nat_lit 8) (Nat.div (Nat.mod v (nat_lit 12)) (nat_lit 3))) (Nat.mod x (nat_lit 4)))

@[expose] noncomputable def betaW (T A : Nat → Nat) (g gi i x : Nat) : Nat :=
  mulC T (mulC T g (betaRepC A i x)) gi

@[expose] noncomputable def betaC (T A : Nat → Nat) (t i x : Nat) : Nat :=
  betaW T A (Nat.mul (nat_lit 16) t) (invC T (Nat.mul (nat_lit 16) t)) i x

@[expose] noncomputable def boundsOK (T A : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 64) fun k => allN (nat_lit 64) fun l => Nat.blt (ent T k l) (nat_lit 3072),
    allN (nat_lit 36) fun i => allN (nat_lit 66) fun k => Nat.blt (ent A i k) (nat_lit 3072))

end CFSG.KC.L34W

end
