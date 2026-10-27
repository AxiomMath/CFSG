module

public import Certificates.Data.Kernel.Co1M.InvFam

public section

namespace CFSG.KC.Graph65

open CFSG.KLie.CT CFSG.KC.Co1F2 CFSG.KC.M1F2

@[expose] noncomputable def clsEq (V : Nat → Nat) (w y : Nat) : Bool :=
  orB (Nat.beq w (V y)) (Nat.beq w (Nat.xor (V y) (nat_lit 2)))

@[expose] noncomputable def eqvK (GT : Nat) (V : Nat → Nat) (n : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun y _ ih x => andB (Nat.blt y n) (andB (clsEq V (vmF (nat_lit 24) GT (V x)) y)
      (ih (Nat.succ x)))) L

@[expose] noncomputable def vertK (mem : Nat → Bool) (V : Nat → Nat) (n : Nat) : Bool :=
  allN n fun x => andB (Nat.blt (V x) (pw2 (nat_lit 24)))
    (andB (mem (V x)) (mem (Nat.xor (V x) (nat_lit 2))))

@[expose] noncomputable def keyK (v : Nat) : Nat := Nat.min v (Nat.xor v (nat_lit 2))

@[expose] noncomputable def sortK (V KS : Nat → Nat) (n : Nat) : Bool :=
  allN n fun k => (fun r => andB (Nat.blt (Nat.shiftRight r (nat_lit 24)) n)
    (andB (Nat.beq (keyK (V (Nat.shiftRight r (nat_lit 24)))) (Nat.land r (maskN (nat_lit 24))))
      (orB (Nat.ble n (Nat.succ k))
        (Nat.blt (Nat.land r (maskN (nat_lit 24))) (Nat.land (KS (Nat.succ k)) (maskN (nat_lit 24)))))))
    (KS k)

@[expose] noncomputable def adjB (L : Nat → Nat) (u : Nat) : Bool :=
  orB (andB (Nat.beq (L u) (nat_lit 3)) (Nat.beq (L (Nat.xor u (nat_lit 2))) (nat_lit 1)))
    (andB (Nat.beq (L (Nat.xor u (nat_lit 2))) (nat_lit 3)) (Nat.beq (L u) (nat_lit 1)))

end CFSG.KC.Graph65

end
