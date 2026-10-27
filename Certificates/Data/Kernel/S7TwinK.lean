module

public import Certificates.Data.Kernel.KGC31P

public section

namespace CFSG.KC.S7TwinK

open CFSG.KC.Enum CFSG.KS CFSG.KC.KGC31P

variable (n w : Nat)

@[expose] noncomputable def pspan (R Ri Y Yi : Nat) : List Nat :=
  [pidn n w, pc n w R R, R, Ri, Y, Yi, pc n w R Y, pc n w Y R]

@[expose] def pmem (L : List Nat) (X : Nat) : Bool := L.any (Nat.beq X)

@[expose] noncomputable def psqOne (A : Nat) : Bool := Nat.beq (pc n w A A) (pidn n w)

@[expose] noncomputable def pq8Pair (R Ri Y : Nat) : Bool :=
  Nat.beq (pc n w R R) (pc n w Y Y) && Nat.beq (pc n w R Y) (pc n w Y Ri)

@[expose] noncomputable def pq8Rel (X Xi Y Yi : Nat) : Bool :=
  Nat.beq (pc n w (pc n w X X) (pc n w X X)) (pidn n w) && !Nat.beq (pc n w X X) (pidn n w) &&
    Nat.beq (pc n w X X) (pc n w Y Y) && Nat.beq (pc n w (pc n w Yi X) Y) Xi

@[expose] noncomputable def ppairWit (sp0 sp : List Nat) (R C Ci : Nat) : Bool :=
  (sp.map (pcj n w C Ci)).all (pmem sp0) ||
    ((sp.map (pcj n w C Ci)).any (fun x => !pmem sp x) &&
      sp.any (fun a => !psqOne n w a && pmem (sp.map (pcj n w C Ci)) a)) ||
    (pmem (sp.map (pcj n w C Ci)) (pc n w R R) &&
      sp.all (fun a => psqOne n w a || !pmem (sp.map (pcj n w C Ci)) a) &&
      sp.any fun k => (sp.map (pcj n w C Ci)).any fun v => !Nat.beq (pc n w k v) (pc n w v k))

@[expose] noncomputable def prepY (sp0 : List Nat) (R : Nat) (cands : List (Nat × Nat)) (Y : Nat) :
    Bool :=
  !pq8Pair n w R (pinv n w R) Y ||
    cands.any fun c => ppairWit n w sp0 (pspan n w R (pinv n w R) Y (pinv n w Y)) R c.1 c.2

@[expose] noncomputable def pairsY (sp0 reps : List Nat) (cands : List (List (Nat × Nat)))
    (Y : Nat) : Bool :=
  (reps.zip cands).all fun p => prepY n w sp0 p.1 p.2 Y

end CFSG.KC.S7TwinK

end
