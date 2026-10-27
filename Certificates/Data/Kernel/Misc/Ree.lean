module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Misc.Ree

open CFSG.KC.Loop

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def red3 (M15 x : Nat) : Nat :=
  Nat.sub x (Nat.mul (nat_lit 3)
    (Nat.land (Nat.shiftRight (Nat.mul x (nat_lit 43691)) (nat_lit 17)) M15))

@[expose] noncomputable def normK (sk G M15 ML fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun N => N)
    (fun _ ih N => strictN (Nat.shiftRight N sk) (fun H =>
      nIf(Nat.beq H (nat_lit 0), N,
        strictN (red3 M15 (Nat.add (Nat.land N ML) (Nat.mul H G))) ih))) fuel

@[expose] noncomputable def mulK (sk G M15 ML fuel a b : Nat) : Nat :=
  normK sk G M15 ML fuel (red3 M15 (Nat.mul a b))

@[expose] noncomputable def powK (sk G M15 ML fuel a e nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun j ih acc => strictN (mulK sk G M15 ML fuel acc acc) (fun sq =>
      strictN (nIf(Nat.blt (nat_lit 0) (Nat.land e (Nat.shiftLeft (nat_lit 1) j)),
        mulK sk G M15 ML fuel sq a, sq)) ih)) nb (nat_lit 1)

@[expose] noncomputable def bitsLe (e nb : Nat) : Bool := Nat.beq (Nat.shiftRight e nb) (nat_lit 0)

@[expose] noncomputable def addK (M15 x y : Nat) : Nat := red3 M15 (Nat.add x y)

@[expose] noncomputable def subK (M15 x y : Nat) : Nat :=
  red3 M15 (Nat.add x (Nat.add y y))

@[expose] noncomputable def repK (L v : Nat) : Nat :=
  Nat.mul v (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 32) L)) (nat_lit 1))
    (nat_lit 4294967295))

@[expose] noncomputable def setupK (k F G M15 ML : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 1) k, bAnd(Nat.blt k (nat_lit 16384),
  bAnd(Nat.beq ML (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 32) k)) (nat_lit 1)),
  bAnd(Nat.beq M15 (repK (Nat.add (Nat.add k k) (nat_lit 2)) (nat_lit 32767)),
  bAnd(Nat.beq (Nat.shiftRight F (Nat.mul (nat_lit 32) k)) (nat_lit 1),
  bAnd(Nat.beq (Nat.land F (repK k (nat_lit 4294967292))) (nat_lit 0),
  bAnd(Nat.beq (red3 M15 (Nat.land F ML)) (Nat.land F ML),
    Nat.beq G (red3 M15 (Nat.add (Nat.land F ML) (Nat.land F ML))))))))))

@[expose] noncomputable def rootK (k G M15 ML nb : Nat) : Bool :=
  strictB (Nat.pow (nat_lit 3) k) (fun q => bAnd(bitsLe q nb,
    Nat.beq (powK (Nat.mul (nat_lit 32) k) G M15 ML (Nat.add k k) (nat_lit 4294967296) q nb)
      (nat_lit 4294967296)))

@[expose] noncomputable def skipB (k b : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true false
        (Nat.beq (Nat.gcd (Nat.add (Nat.pow (nat_lit 3) b) (nat_lit 2))
          (Nat.sub (Nat.pow (nat_lit 3) k) (nat_lit 1))) (nat_lit 1)))
      true (Nat.beq (Nat.mod (Nat.add b b) k) (nat_lit 1)))
    (Nat.beq (Nat.gcd b k) (nat_lit 1))

@[expose] noncomputable def arithK (k b s a : Nat) : Bool :=
  strictB (Nat.sub (Nat.pow (nat_lit 3) k) (nat_lit 1)) (fun q1 =>
  strictB (Nat.pow (nat_lit 3) b) (fun sb =>
  bAnd(Nat.beq (Nat.mod (Nat.mul (Nat.add sb (nat_lit 2)) s) q1) (nat_lit 1),
  bAnd(Nat.beq (Nat.mod (Nat.mul (Nat.add sb (nat_lit 1)) a) q1) (nat_lit 2),
  bAnd(Nat.beq (Nat.mod a (nat_lit 2)) (nat_lit 0),
  bAnd(Nat.beq (Nat.mod q1 (nat_lit 2)) (nat_lit 0),
  bAnd(Nat.beq (Nat.mod (Nat.div q1 (nat_lit 2)) (nat_lit 2)) (nat_lit 1),
  bAnd(Nat.beq (Nat.mod (Nat.add sb (nat_lit 1)) (nat_lit 2)) (nat_lit 0),
    Nat.beq (Nat.gcd (Nat.div (Nat.add sb (nat_lit 1)) (nat_lit 2)) (Nat.div q1 (nat_lit 2)))
      (nat_lit 1)))))))))

@[expose] noncomputable def caseB (k G M15 ML b s a w ns na nq : Nat) : Bool :=
  strictB (Nat.mul (nat_lit 32) k) (fun sk => strictB (Nat.add k k) (fun fu =>
  strictB (Nat.add (Nat.pow (nat_lit 3) b) (nat_lit 1)) (fun e =>
  bAnd(arithK k b s a, bAnd(bitsLe s ns, bAnd(bitsLe a na, bAnd(bitsLe e nq,
  bAnd(Nat.beq (Nat.land w (repK k (nat_lit 4294967292))) (nat_lit 0),
  bAnd(Nat.beq (red3 M15 (Nat.land w ML)) w,
  strictB (powK sk G M15 ML fu (nat_lit 4294967297) s ns) (fun z =>
  strictB (powK sk G M15 ML fu (nat_lit 4294967298) s ns) (fun y =>
  strictB (subK M15 (powK sk G M15 ML fu z e nq) (powK sk G M15 ML fu y e nq)) (fun u =>
  strictB (addK M15 u (nat_lit 2)) (fun um =>
  strictB (addK M15 u (nat_lit 1)) (fun up =>
  strictB (powK sk G M15 ML fu um a na) (fun A =>
  strictB (powK sk G M15 ML fu up a na) (fun C =>
  strictB (red3 M15 (Nat.add (Nat.add (mulK sk G M15 ML fu z A)
      (Nat.mul (nat_lit 2) (mulK sk G M15 ML fu (addK M15 (Nat.add z (Nat.add y y)) (nat_lit 1))
        (powK sk G M15 ML fu u a na))))
    (Nat.add (Nat.mul (nat_lit 2) (mulK sk G M15 ML fu y C)) (mulK sk G M15 ML fu A C))))
    (fun T =>
  strictB (mulK sk G M15 ML fu (mulK sk G M15 ML fu (mulK sk G M15 ML fu u um) up) T) (fun P =>
    Nat.beq (mulK sk G M15 ML fu P w) (nat_lit 1)))))))))))))))))))

end CFSG.KC.Misc.Ree

end
