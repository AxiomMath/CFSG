module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.PermSLP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def lo (g : Nat) : Nat := Nat.land g (nat_lit 65535)

@[expose] noncomputable def hi (g : Nat) : Nat := Nat.shiftRight g (nat_lit 16)

@[expose] noncomputable def letZ (s : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.ofNat (Nat.succ (Nat.shiftRight s (nat_lit 1))))
    (Int.negSucc (Nat.shiftRight s (nat_lit 1))) (Nat.beq (Nat.land s (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def symV (nL : Nat) (S SI V : Nat → Nat) (s : Nat) : Nat :=
  nIf(Nat.blt s nL,
    nIf(Nat.beq (Nat.land s (nat_lit 1)) (nat_lit 0), S (Nat.shiftRight s (nat_lit 1)),
      SI (Nat.shiftRight s (nat_lit 1))),
    V (Nat.sub s nL))

@[expose] noncomputable def appK (a b : List Int) : List Int :=
  List.rec (motive := fun _ => List Int) b (fun x _ ih => x :: ih) a

@[expose] noncomputable def symE (nL : Nat) (G : Nat → Nat) (f : Nat) : Nat → List Int :=
  Nat.rec (motive := fun _ => Nat → List Int) (fun _ => [])
    (fun _ ih s => Bool.rec (motive := fun _ => List Int)
      (appK (ih (lo (G (Nat.sub s nL)))) (ih (hi (G (Nat.sub s nL)))))
      [letZ s] (Nat.blt s nL)) f

@[expose] noncomputable def letK (n w nL : Nat) (S SI V : Nat → Nat) (s : Nat) : Bool :=
  Nat.beq (wordK n w (mask w) (pidn n w) S SI [letZ s]) (symV nL S SI V s)

@[expose] noncomputable def ruleK (n w nL : Nat) (S SI V G : Nat → Nat) (k : Nat) : Bool :=
  bAnd(Nat.blt (lo (G k)) (Nat.add nL k), bAnd(Nat.blt (hi (G k)) (Nat.add nL k),
    Nat.beq (pcomp n w (mask w) (symV nL S SI V (lo (G k))) (symV nL S SI V (hi (G k)))) (V k)))

@[expose] noncomputable def topK (nL R f : Nat) (G : Nat → Nat) (t : Nat) (wd : List Int) : Bool :=
  bAnd(Nat.blt t (Nat.add nL R), symE nL G f t == wd)

end CFSG.KC.PermSLP

end
