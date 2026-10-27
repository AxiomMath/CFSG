module

public import Certificates.Data.Kernel.Misc.ChainTail

public section

namespace CFSG.KC.Misc.ChainTail

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def repBranchK (n w : Nat) (LR TR : Nat → Nat) (BP X : Nat)
    (XP : Nat → Nat) (rels : List (Nat × Nat × Nat)) (NE : Nat) (EP : Nat → Nat) (nb q : Nat) :
    Bool :=
  relOKK w (mask w) BP XP rels 0 (pidn n w) (rpt w (mask w) (LR 0) q) &&
    ptailBranchK n w LR TR BP X XP rels NE EP nb q

@[expose] noncomputable def orbRelK (n w : Nat) (LR : Nat → Nat) (BP : Nat) (XP : Nat → Nat)
    (rels : List (Nat × Nat × Nat)) (NE : Nat) (EP : Nat → Nat) (NR : Nat) (RB RI EK : Nat → Nat)
    (k : Nat) : Bool :=
  !(relOKK w (mask w) BP XP rels 0 (pidn n w) (rpt w (mask w) (LR 0) k)) ||
    (Nat.blt (RI k) NR && Nat.blt (RB (RI k)) (rcnt (LR 0)) && Nat.blt (EK k) NE &&
      Nat.beq (pg w (mask w) (EP (EK k)) (rpt w (mask w) (LR 0) (RB (RI k))))
        (rpt w (mask w) (LR 0) k))

end CFSG.KC.Misc.ChainTail

end
