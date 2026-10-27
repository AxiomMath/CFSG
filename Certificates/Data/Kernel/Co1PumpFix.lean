module

public import Certificates.Data.Kernel.SporSch.Co1Mat

public section

namespace CFSG.KC.Co1Pairs

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24

@[expose] noncomputable def nrowK (M i : Nat) : Nat := Nat.xor (rowK M i) (Nat.shiftLeft 1 i)

@[expose] noncomputable def selK (M c : Nat) : Nat :=
  foldN (nat_lit 24) (fun i s => nIf(hasBit c i, Nat.xor s (nrowK M i), s)) (nat_lit 0)

@[expose] noncomputable def entK (M J q : Nat) (e : Nat × Nat × Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (bAnd(Nat.beq (Nat.land e.2.1 J) e.2.1,
      Nat.beq (selK M e.1) (Nat.xor (Nat.shiftLeft 1 q) e.2.1)))
    (bAnd(Nat.beq (actK M e.2.2) e.2.2, Nat.beq (Nat.land e.2.2 J) (Nat.shiftLeft 1 q)))
    (hasBit J q)

@[expose] noncomputable def entsK (M J : Nat) : List (Nat × Nat × Nat) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun q => Nat.beq q 24)
    (fun e _ ih q => bAnd(entK M J q e, ih (Nat.succ q)))

@[expose] noncomputable def cntK (mem : Nat → Bool) (J : Nat) :
    List (Nat × Nat × Nat) → Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun _ x acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (mem x))
    (fun e _ ih q x acc => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ q) x acc)
      (ih (Nat.succ q) (Nat.xor x e.2.2) (ih (Nat.succ q) x acc)) (hasBit J q))

@[expose] noncomputable def popK (J : Nat) : Nat :=
  foldN (nat_lit 24) (fun i s => nIf(hasBit J i, Nat.succ s, s)) (nat_lit 0)

end CFSG.KC.Co1Pairs

end
