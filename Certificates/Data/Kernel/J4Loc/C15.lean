module

public import Certificates.Data.Kernel.J4Loc.Trio

public section

namespace CFSG.KC.J4Loc

open CFSG.KC.J4Q CFSG.KC.Loop

@[expose] noncomputable def idxW (TR : Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun i => i)
    (fun l _ ih i => ih (fld (nat_lit 12) (fld (nat_lit 96) TR i) l)) w

@[expose] noncomputable def hasZ (TK i : Nat) : Bool :=
  bitB (keyK (octL (fld (nat_lit 80) TK i))) (nat_lit 1131)

@[expose] noncomputable def cntZ (TK N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e acc => strictN acc fun a => Bool.rec (motive := fun _ => Nat) a (Nat.succ a) (hasZ TK e)) N

@[expose] noncomputable def zOK (TR : Nat) (wa wb : List Nat) (i : Nat) : Bool :=
  strictB (idxW TR wa i) fun a => strictB (idxW TR wb i) fun b =>
    andB (Nat.beq (idxW TR wa b) (idxW TR wb a))
      (andB (Nat.beq (idxW TR wa (idxW TR wa a)) i) (Nat.beq (idxW TR wb (idxW TR wb b)) i))

@[expose] noncomputable def neZ (TR : Nat) (wa wb : List Nat) (i : Nat) : Bool :=
  strictB (idxW TR wa i) fun a => strictB (idxW TR wb i) fun b =>
    andB (notB (Nat.beq a i)) (andB (notB (Nat.beq b i))
      (andB (notB (Nat.beq b a)) (notB (Nat.beq b (idxW TR wa a)))))

@[expose] noncomputable def c15K (TK TR N : Nat) (wa wb : List Nat) : Bool :=
  andB (Nat.beq (cntZ TK N) (nat_lit 15))
    (andB (CFSG.KC.Enum.allN N fun i => orB (notB (hasZ TK i)) (zOK TR wa wb i))
      (anyK N fun i => andB (hasZ TK i) (neZ TR wa wb i)))

end CFSG.KC.J4Loc

end
