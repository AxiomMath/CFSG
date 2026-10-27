module

public import Certificates.Data.Kernel.Co1PairsRep
public import Certificates.Data.Kernel.SporSch.Co1MatW

public section

namespace CFSG.KC.Co1Pairs

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CFSG.KC.Co1B

@[expose] noncomputable def dig3 (k : Nat) : List Nat :=
  [Nat.mod (Nat.div k 243) 3, Nat.mod (Nat.div k 81) 3, Nat.mod (Nat.div k 27) 3,
    Nat.mod (Nat.div k 9) 3, Nat.mod (Nat.div k 3) 3, Nat.mod k 3]

@[expose] noncomputable def conjOK (M MI : Nat → Nat) (w : List Nat) (X A B : Nat) : Bool :=
  bAnd(lettersK (nat_lit 75) w, bAnd(Nat.beq (wordWK M MI w) X,
    Nat.beq (mulWK X A) (mulWK B X)))

@[expose] noncomputable def depK (D k : Nat) : Nat :=
  Nat.land (Nat.shiftRight D (Nat.mul 5 k)) 31

@[expose] noncomputable def rootK (j : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (Nat.beq j 324) true
    (Nat.beq j 81)) true (Nat.beq j 243)

@[expose] noncomputable def recOK (gs : List Nat) (G : Nat → Nat) (D j p g : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (bAnd(Nat.blt 0 p, bAnd(Nat.blt p 729, bAnd(Nat.blt g 3, bAnd(Nat.blt (depK D p) (depK D j),
      Nat.beq (mulWK (G g) (eltK gs (dig3 p))) (mulWK (eltK gs (dig3 j)) (G g)))))))
    true (bAnd(Nat.beq p j, rootK j))

@[expose] noncomputable def fusOK (gs : List Nat) (G : Nat → Nat) (D : Nat) :
    List (Nat × Nat) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k 729)
    (fun r _ ih k => bAnd(recOK gs G D k r.1 r.2, ih (Nat.succ k)))

end CFSG.KC.Co1Pairs

end
