module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.Fi22Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def c (p q : Nat) : Nat := pcomp 3510 12 (mask 12) p q

@[expose] noncomputable def inv (p : Nat) : Nat := pinvS 3510 12 (mask 12) p

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 3510 12 (mask 12) (3510 * 12) p

@[expose] noncomputable def pk (p : Nat) : Bool := permOK 3510 12 (mask 12) (3510 * 12) p (inv p)

@[expose] noncomputable def idP : Nat := pidn 3510 12

@[expose] noncomputable def toInt (x : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.negSucc (x / 2 - 1)) (Int.ofNat (x / 2))
    (Nat.beq (x % 2) 0)

@[expose] noncomputable def wd (S SI : Nat → Nat) (w : List Nat) : Nat :=
  wordK 3510 12 (mask 12) idP S SI (w.map toInt)

@[expose] noncomputable def lt (w : List Nat) (j : Nat) : Bool := lettersK j (w.map toInt)

@[expose] noncomputable def inT (N : Nat) (T : Nat → Nat) (x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(Nat.beq x (T i), true, ih)) N

@[expose] noncomputable def conjK (n ng : Nat) (G : Nat → Nat) (N : Nat) (T : Nat → Nat) : Bool :=
  allN ng fun k => bAnd(inT N T (c (c n (G k)) (inv n)), inT N T (c (c (inv n) (G k)) n))

@[expose] noncomputable def elemK (ng : Nat) (G : Nat → Nat) : Bool :=
  allN ng fun i => bAnd(Nat.beq (c (G i) (c (G i) (G i))) idP,
    allN ng fun j => Nat.beq (c (G i) (G j)) (c (G j) (G i)))

end CFSG.KC.Fi22Cover

end
