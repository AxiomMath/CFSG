module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.PMem

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

@[expose] noncomputable def atK (cnt : Nat) (T POS : Nat → Nat) (i Q : Nat) : Bool :=
  strictB (r32 POS i) (fun q => bAnd(Nat.blt q cnt, Nat.beq (T q) Q))

@[expose] noncomputable def conjInK (n w m cnt : Nat) (T POS A AI B : Nat → Nat) (ka kb : Nat) :
    Bool :=
  allN ka (fun i => allN kb (fun j => atK cnt T POS (Nat.add (Nat.mul i kb) j)
    (pcomp n w m (pcomp n w m (A i) (B j)) (AI i))))

@[expose] noncomputable def commInK (n w m cnt : Nat) (T POS A AI : Nat → Nat) (ka : Nat) : Bool :=
  allN ka (fun i => allN ka (fun j => atK cnt T POS (Nat.add (Nat.mul i ka) j)
    (pcomp n w m (pcomp n w m (pcomp n w m (A i) (A j)) (AI i)) (AI j))))

@[expose] noncomputable def commAllK (n w m k : Nat) (G : Nat → Nat) (p : Nat) : Bool :=
  allN k (fun j => Nat.beq (pcomp n w m p (G j)) (pcomp n w m (G j) p))

@[expose] noncomputable def centOneK (n w m idn cnt : Nat) (T : Nat → Nat) (k : Nat)
    (G : Nat → Nat) : Bool :=
  allN cnt (fun i => bIf(commAllK n w m k G (T i), Nat.beq (T i) idn, true))

@[expose] noncomputable def filtInK (n w m cnt : Nat) (T : Nat → Nat) (k : Nat) (G : Nat → Nat)
    (cnt' : Nat) (T' POS : Nat → Nat) : Bool :=
  allN cnt (fun i => bIf(commAllK n w m k G (T i), atK cnt' T' POS i (T i), true))

@[expose] noncomputable def commToK (n w m cnt : Nat) (T POS : Nat → Nat) (cnt' : Nat)
    (T' POS' : Nat → Nat) (z : Nat) : Bool :=
  strictB (r32 POS (nat_lit 0)) (fun p => strictB (r32 POS' (nat_lit 0)) (fun q =>
    bAnd(Nat.blt p cnt, bAnd(Nat.blt q cnt',
      Nat.beq (pcomp n w m (T p) (T' q)) (pcomp n w m (pcomp n w m z (T' q)) (T p))))))

@[expose] noncomputable def notCentK (n w m nw cnt : Nat) (T POS : Nat → Nat) (z k : Nat)
    (G : Nat → Nat) : Bool :=
  strictB (r32 POS (nat_lit 0)) (fun p => bAnd(Nat.blt p cnt,
    bAnd(commK n w m nw (T p) z, bIf(commAllK n w m k G (T p), false, true))))

end CFSG.KS.PMem

end
