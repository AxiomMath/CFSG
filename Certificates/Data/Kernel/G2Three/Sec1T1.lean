module

public import Certificates.Data.Kernel.G2Three.Sec1

public section

namespace CFSG.KD.G2Three.Sec1

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.G2Three

@[expose] noncomputable def SWP (a : Nat) : Nat :=
  Nat.add (Nat.shiftRight a 392) (Nat.shiftLeft (Nat.land a LP) 392)

@[expose] noncomputable def closF (f : Nat → Nat → Nat) (X G POS : Nat → Nat) (n k lo m hi : Nat) :
    Bool :=
  allBelow m hi fun j => (fun i =>
    bAnd(Nat.blt (POS i) n, Nat.beq (X (POS i)) (f (X (Nat.div i k)) (G (Nat.mod i k)))))
    (Nat.add lo j)

@[expose] noncomputable def dg3 (c p : Nat) : Nat := Nat.mod (Nat.div c p) 3

@[expose] noncomputable def MUL22 (a b : Nat) : Nat :=
  Nat.add
    (Nat.add (Nat.mod (Nat.add (Nat.mul (dg3 a 1) (dg3 b 1)) (Nat.mul (dg3 a 3) (dg3 b 9))) 3)
      (Nat.mul 3
        (Nat.mod (Nat.add (Nat.mul (dg3 a 1) (dg3 b 3)) (Nat.mul (dg3 a 3) (dg3 b 27))) 3)))
    (Nat.add
      (Nat.mul 9
        (Nat.mod (Nat.add (Nat.mul (dg3 a 9) (dg3 b 1)) (Nat.mul (dg3 a 27) (dg3 b 9))) 3))
      (Nat.mul 27
        (Nat.mod (Nat.add (Nat.mul (dg3 a 9) (dg3 b 3)) (Nat.mul (dg3 a 27) (dg3 b 27))) 3)))

@[expose] noncomputable def MUL3 (p q : Nat) : Nat :=
  Nat.add (fld(p, Nat.mul 2 (fld(q, 0, 3)), 3))
    (Nat.add (Nat.shiftLeft (fld(p, Nat.mul 2 (fld(q, 2, 3)), 3)) 2)
      (Nat.shiftLeft (fld(p, Nat.mul 2 (fld(q, 4, 3)), 3)) 4))

@[expose] noncomputable def MUL33 (x y : Nat) : Nat :=
  Nat.add (MUL3 (Nat.land x 63) (Nat.land y 63))
    (Nat.shiftLeft (MUL3 (Nat.shiftRight x 6) (Nat.shiftRight y 6)) 6)

@[expose] noncomputable def cntMK (X A B C : Nat → Nat) (k n hi : Nat) : Nat :=
  sumBelow n hi fun i => strictN (X i) fun x =>
    nIf(allR k fun s => strictB (MULP x (A s)) fun y =>
      bIf(Nat.beq y (MULP (B s) x), true, Nat.beq y (MULP (C s) x)), 1, 0)

end CFSG.KD.G2Three.Sec1

end
