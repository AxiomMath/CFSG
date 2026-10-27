module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.DceS

public section

namespace CFSG.KC.ThU

open CFSG.KC.Th CFSG.KC.Th.BigS

@[expose] noncomputable def prodR {m : Nat} (RB : Nat → Nat) (c rm ONE GR : Nat) :
    List (Fin m × Bool) → Nat :=
  List.rec (motive := fun _ => Nat) ONE
    (fun l _ acc => mulB c rm (RB (regAt GR l.1.val)) acc)

@[expose] noncomputable def relOKR {m : Nat} (RB : Nat → Nat) (c rm ONE GR : Nat)
    (r : List (Fin m × Bool)) : Bool :=
  andB (r.all fun l => l.2) (Nat.beq (prodR RB c rm ONE GR r) ONE)

@[expose] noncomputable def blockB (RB PT : Nat → Nat) (rm PR n fr tb p tc sc : Nat) : Bool :=
  andB (Nat.blt (PT 0) (2 ^ 248)) (andB (baseFixed RB rm PR (PT 0) tb n) (andB
    (Nat.beq (runTree RB PT rm PR fr tb [tc] 2) (p ^ (tb - fr) + 1))
    (Nat.beq (DceS.sortedCount (DceS.runSorted PT 11 (p ^ (tb - fr)) [sc] 1)) (p ^ (tb - fr)))))

@[expose] noncomputable def gmask3 (GR : Nat) : Nat :=
  2 ^ regAt GR 0 ||| 2 ^ regAt GR 1 ||| 2 ^ regAt GR 2

end CFSG.KC.ThU

end
