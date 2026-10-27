module

public import Certificates.Data.Kernel.BabyMonster.CTIB.CosetQ

public section

namespace CFSG.KC.BM.OrbT

open CFSG.KC.BM CFSG.KC.BM.CosetQ

@[expose] noncomputable def fld16 (E i : Nat) : Nat :=
  Nat.land (Nat.shiftRight E (Nat.mul (nat_lit 16) i)) (nat_lit 65535)

@[expose] noncomputable def tPar (t : Nat) : Nat := Nat.land t (nat_lit 4095)

@[expose] noncomputable def tLab (t : Nat) : Nat := Nat.land (Nat.shiftRight t (nat_lit 12)) (nat_lit 63)

@[expose] noncomputable def tDep (t : Nat) : Nat := Nat.shiftRight t (nat_lit 18)

@[expose] noncomputable def incPt (n bound S i : Nat) : Bool :=
  andB (Nat.blt (fld32 S i) bound)
    (Bool.rec (motive := fun _ => Bool) true (Nat.blt (fld32 S i) (fld32 S (Nat.succ i)))
      (Nat.blt (Nat.succ i) n))

@[expose] noncomputable def imgOK (act : Nat → Nat → Nat) (n S i k j : Nat) : Bool :=
  andB (Nat.blt j n) (Nat.beq (act k (fld32 S i)) (fld32 S j))

@[expose] noncomputable def closPt (act : Nat → Nat → Nat) (ngen n S E i : Nat) : Bool :=
  allLt ngen fun k => imgOK act n S i k (fld16 E (Nat.add (Nat.mul ngen i) k))

@[expose] noncomputable def edgeOK (act : Nat → Nat → Nat) (ngen n S T i t : Nat) : Bool :=
  andB (Nat.blt (tPar t) n) (andB (Nat.blt (tLab t) ngen)
    (andB (Nat.beq (Nat.succ (tDep (fld32 T (tPar t)))) (tDep t))
      (Nat.beq (act (tLab t) (fld32 S (tPar t))) (fld32 S i))))

@[expose] noncomputable def treePt (act : Nat → Nat → Nat) (ngen n r S T i : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (edgeOK act ngen n S T i (fld32 T i)) (Nat.beq i r)
    (Nat.beq (tDep (fld32 T i)) (nat_lit 0))

@[expose] noncomputable def fuseK (LO AH : Nat) (Gs Ds : List Nat) (k x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (mulQ LO (nthN Ds (Nat.sub k (nat_lit 22))) (autQ LO (nthN Gs (Nat.sub k (nat_lit 22))) x))
    (mulQ LO (fld32 AH k) (mulQ LO x (Nat.pow (nat_lit 2) k)))
    (Nat.blt k (nat_lit 22))

@[expose] noncomputable def yActK (LO : Nat) (Ys Fs : List Nat) (j x : Nat) : Nat :=
  (fun f => mulQ LO (mulQ LO (mulQ LO (mulQ LO f f) f) (autQ LO (nthN Ys j) x)) f) (nthN Fs j)

end CFSG.KC.BM.OrbT

end
