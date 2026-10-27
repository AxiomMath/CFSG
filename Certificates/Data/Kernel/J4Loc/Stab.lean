module

public import Certificates.Data.Kernel.J4Loc.Trio

public section

namespace CFSG.KC.J4Loc

open CFSG.KC.J4Q CFSG.KC.Loop

@[expose] noncomputable def wordAct (LR : List (List Nat)) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun l _ ih => actK (rowL LR l) ih) w

@[expose] noncomputable def stabRowOK (LR : List (List Nat)) (e : Nat × Nat × Nat × List Nat) :
    Bool :=
  andB (allL e.2.2.2 fun l => Nat.blt l (nat_lit 6))
    (andB (Nat.beq (wordAct LR e.2.2.2 (nat_lit 422)) e.1)
      (andB (Nat.beq (wordAct LR e.2.2.2 (nat_lit 553)) e.2.1)
        (Nat.beq (wordAct LR e.2.2.2 (nat_lit 1131)) e.2.2.1)))

@[expose] noncomputable def stabOK (LR : List (List Nat)) (S : List (Nat × Nat × Nat × List Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => andB (stabRowOK LR e) ih) S

@[expose] noncomputable def stabHas (S : List (Nat × Nat × Nat × List Nat)) (a b c : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun e _ ih => orB (andB (Nat.beq e.1 a) (andB (Nat.beq e.2.1 b) (Nat.beq e.2.2.1 c))) ih) S

@[expose] noncomputable def stabCov (V : List Nat) (S : List (Nat × Nat × Nat × List Nat)) : Bool :=
  allL V fun a => allL V fun b => allL V fun c =>
    orB (Nat.beq a (nat_lit 0)) (orB (Nat.beq b (nat_lit 0)) (orB (Nat.beq b a)
      (orB (Nat.beq c (nat_lit 0)) (orB (Nat.beq c a) (orB (Nat.beq c b)
        (orB (Nat.beq c (Nat.xor a b)) (stabHas S a b c)))))))

end CFSG.KC.J4Loc

end
