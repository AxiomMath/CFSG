module

public import Certificates.Data.Kernel.Spor.SlpPlan

public section

namespace CFSG.KC.SlpM

open CFSG.KC.Loop CFSG.KC.Ord

@[expose] noncomputable def nilB {α : Type} (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l

@[expose] noncomputable def invOut (mul : Nat → Nat → Nat) (ONE : Nat) (VLD : Nat → Bool)
    (R : Nat → Nat) (nR : Nat) (PC PN LY : Nat → Nat) (base k : Nat) (p : Nat × Nat) : Bool :=
  (fun r => andB (andB (oddN p.1) (andB (Nat.blt (nat_lit 0) r) (Nat.blt r nR)))
    (andB (andB (Nat.beq (PN r) (Nat.sub p.1 (nat_lit 1))) (andB (Nat.blt (PC r) k)
      (orB (Nat.beq (LY (PC r)) (LY k)) (Nat.blt (Nat.sub p.1 (nat_lit 1)) base))))
      (andB (VLD (R p.2)) (Nat.beq (mul (R p.2) (R r)) ONE))))
    (Nat.sub p.2 (nat_lit 1))

@[expose] noncomputable def invOK (mul : Nat → Nat → Nat) (ONE : Nat) (VLD : Nat → Bool)
    (R : Nat → Nat) (nR : Nat) (PC PN LY : Nat → Nat) (base k : Nat) (outs : List (Nat × Nat))
    (eqs neqs : List (List Nat × List Nat)) : Bool :=
  andB (allL outs (invOut mul ONE VLD R nR PC PN LY base k)) (andB (nilB eqs) (nilB neqs))

end CFSG.KC.SlpM

end
