module

public import Certificates.Data.Kernel.LyOmega.Small

public section

namespace CFSG.KC.LyOm

open CFSG.KC.Loop CFSG.KC.LL CFSG.KC.Ord

@[expose] noncomputable def sQuad (C : SConsts) (a b c X : Nat) : Nat :=
  redP (nat_lit 11) C.L7 C.H7 (nat_lit 5) (nat_lit 7)
    (Nat.add (Nat.mul a (sMul C X X)) (Nat.add (Nat.mul b X) (Nat.mul c C.ONE)))

@[expose] noncomputable def sConjTree (C : SConsts) (G Z P L : Nat → Nat) (Y m n : Nat) : Bool :=
  bAnd(Nat.beq (Z (nat_lit 0)) Y,
  bAnd(allBelow n n (fun k => bAnd(sVld C (Z k), bIf(Nat.beq k (nat_lit 0), true,
      bAnd(Nat.blt (P k) k, bAnd(Nat.blt (L k) m,
        Nat.beq (sMul C (G (L k)) (Z (P k))) (sMul C (Z k) (G (L k)))))))),
    allBelow (Nat.mul n n) (Nat.succ (Nat.shiftRight (Nat.mul n n) (nat_lit 6))) (fun t =>
      (fun i j => bIf(Nat.blt i j, bIf(Nat.beq (Z i) (Z j), false, true), true))
        (Nat.div t n) (Nat.mod t n))))

end CFSG.KC.LyOm

end
