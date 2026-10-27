module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.SetOrb

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def maskK (w len C : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (pg w (mask w) C t))) len

@[expose] noncomputable def imgK (w len P C : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (pg w (mask w) P (pg w (mask w) C t))))
    len

@[expose] noncomputable def keyK (b w len C : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => Nat.add (Nat.mul acc b) (pg w (mask w) C t)) len

@[expose] noncomputable def codeOK (n w len C M : Nat) : Bool :=
  bAnd(allN len (fun t => Nat.blt (pg w (mask w) C t) n),
  bAnd(allN (Nat.sub len (nat_lit 1)) (fun t =>
      Nat.blt (pg w (mask w) C t) (pg w (mask w) C (Nat.succ t))),
    Nat.beq (maskK w len C) M))

@[expose] noncomputable def closK (w len ng Np : Nat) (G C M X E : Nat → Nat) (i : Nat) : Bool :=
  allN ng fun k => strictB (pg (nat_lit 16) (mask (nat_lit 16)) (E i) k) fun j =>
    bAnd(Nat.blt j Np, Nat.beq (imgK w len (G k) (C (X i))) (M (X j)))

@[expose] noncomputable def treeK (w len ng : Nat) (G C M X D : Nat → Nat) (i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), true,
    strictB (Nat.mod (D i) (nat_lit 65536)) fun p => strictB (Nat.div (D i) (nat_lit 65536)) fun l =>
      bAnd(Nat.blt p i, bAnd(Nat.blt l ng,
        Nat.beq (imgK w len (G l) (C (X p))) (M (X i)))))

@[expose] noncomputable def eqMaskK (n w P Q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft (nat_lit 1) i))
      (Nat.beq (pg w (mask w) P i) (pg w (mask w) Q i))) n

@[expose] noncomputable def invK (X Y : Nat → Nat) (i : Nat) : Bool := Nat.beq (Y (X i)) i

end CFSG.KC.SetOrb

end
