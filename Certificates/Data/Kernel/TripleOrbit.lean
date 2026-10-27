module

public import CFSG.Certificates.Kernel.Lie.CT.Core
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Triple

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def rec (T : Nat → Nat) (i : Nat) : Nat :=
  fget (T (Nat.shiftRight i (nat_lit 6))) (Nat.land i (nat_lit 63)) (nat_lit 36)

@[expose] noncomputable def code (r : Nat) : Nat := Nat.land r (nat_lit 32767)

@[expose] noncomputable def imgC (G c : Nat) : Nat :=
  Nat.add (fget G (fget c (nat_lit 0) (nat_lit 5)) (nat_lit 5))
    (Nat.add (Nat.mul (nat_lit 32) (fget G (fget c (nat_lit 1) (nat_lit 5)) (nat_lit 5)))
      (Nat.mul (nat_lit 1024) (fget G (fget c (nat_lit 2) (nat_lit 5)) (nat_lit 5))))

@[expose] noncomputable def injC (c : Nat) : Bool :=
  (fun x y z => andB (andB (Nat.blt x (nat_lit 22)) (andB (Nat.blt y (nat_lit 22)) (Nat.blt z (nat_lit 22))))
      (andB (notB (Nat.beq x y)) (andB (notB (Nat.beq x z)) (notB (Nat.beq y z)))))
    (fget c (nat_lit 0) (nat_lit 5)) (fget c (nat_lit 1) (nat_lit 5)) (fget c (nat_lit 2) (nat_lit 5))

@[expose] noncomputable def nodeOK (G0 G1 : Nat) (T : Nat → Nat) (N i : Nat) : Bool :=
  (fun r => (fun c d => andB (injC c)
      (andB (bIf(Nat.blt (Nat.succ i) N, Nat.blt c (code (rec T (Nat.succ i))), true))
        (bIf(Nat.beq d (nat_lit 0), Nat.beq c (nat_lit 2080),
          (fun p => andB (Nat.blt p N) ((fun rp => andB (Nat.beq (Nat.shiftRight rp (nat_lit 30)) (Nat.sub d (nat_lit 1)))
              (Nat.beq (imgC (nIf(Nat.beq (fget r (nat_lit 29) (nat_lit 1)) (nat_lit 0), G0, G1)) (code rp)) c))
            (rec T p)))
          (fget (Nat.shiftRight r (nat_lit 15)) (nat_lit 0) (nat_lit 14))))))
    (code r) (Nat.shiftRight r (nat_lit 30)))
  (rec T i)

@[expose] noncomputable def treeOK (G0 G1 : Nat) (T : Nat → Nat) (N hi : Nat) : Bool :=
  andB (Nat.ble N (Nat.mul (nat_lit 64) hi)) (allBelow N hi (nodeOK G0 G1 T N))

end CFSG.KC.Triple

end
