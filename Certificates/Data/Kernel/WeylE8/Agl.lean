module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum

@[expose] noncomputable def actT (g t : Nat) : Nat :=
  Nat.add (pg (nat_lit 3) (nat_lit 7) g (pg (nat_lit 3) (nat_lit 7) t (nat_lit 0)))
    (Nat.add (Nat.shiftLeft (pg (nat_lit 3) (nat_lit 7) g (pg (nat_lit 3) (nat_lit 7) t (nat_lit 1))) (nat_lit 3))
      (Nat.add (Nat.shiftLeft (pg (nat_lit 3) (nat_lit 7) g (pg (nat_lit 3) (nat_lit 7) t (nat_lit 2))) (nat_lit 6))
        (Nat.shiftLeft (pg (nat_lit 3) (nat_lit 7) g (pg (nat_lit 3) (nat_lit 7) t (nat_lit 3))) (nat_lit 9))))

@[expose] noncomputable def bitK (S t : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight S t) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def stepT (g h S : Nat) : Nat :=
  foldN (nat_lit 4096) (fun t acc => nIf(bitK S t,
    Nat.lor acc (Nat.lor (Nat.shiftLeft (nat_lit 1) (actT g t)) (Nat.shiftLeft (nat_lit 1) (actT h t))),
    acc)) S

@[expose] noncomputable def iterT (g h k S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun _ ih S => strictN (stepT g h S) ih) k S

@[expose] noncomputable def affK (t : Nat) : Bool :=
  strictB (pg (nat_lit 3) (nat_lit 7) t (nat_lit 0)) fun a =>
  strictB (pg (nat_lit 3) (nat_lit 7) t (nat_lit 1)) fun b =>
  strictB (pg (nat_lit 3) (nat_lit 7) t (nat_lit 2)) fun d =>
  strictB (pg (nat_lit 3) (nat_lit 7) t (nat_lit 3)) fun e =>
    bIf(Nat.beq a b, false, bIf(Nat.beq a d, false, bIf(Nat.beq b d, false,
      bIf(Nat.beq e a, false, bIf(Nat.beq e b, false, bIf(Nat.beq e d, false,
        bIf(Nat.beq e (Nat.xor a (Nat.xor b d)), false, true)))))))

@[expose] noncomputable def aglK (g h : Nat) : Bool :=
  strictB (iterT g h (nat_lit 32) (Nat.shiftLeft (nat_lit 1) (nat_lit 2184))) fun O =>
    allN (nat_lit 4096) fun t => bIf(affK t, bitK O t, true)

end CFSG.KLC.E8

end
