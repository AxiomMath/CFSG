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

@[expose] noncomputable def repBranchK1 (n w : Nat) (LR TR : Nat → Nat) (BP X : Nat)
    (XP : Nat → Nat) (rels : List (Nat × Nat × Nat)) (NE : Nat) (EP : Nat → Nat) (nb q0 r : Nat) :
    Bool :=
  ptailK n w LR TR BP X XP rels NE EP (Nat.sub nb 2) 2
    (pcomp n w (mask w) (TR (Nat.add (roff n (Nat.mul n w) (LR 0)) q0))
      (TR (Nat.add (roff n (Nat.mul n w) (LR 1)) r)))

@[expose] noncomputable def orbRelK1 (n w : Nat) (LR TR : Nat → Nat) (BP : Nat) (XP : Nat → Nat)
    (rels : List (Nat × Nat × Nat)) (NE : Nat) (EP : Nat → Nat) (q0 NR : Nat)
    (RB RI EK : Nat → Nat) (k : Nat) : Bool :=
  !(relOKK w (mask w) BP XP rels 1 (TR (Nat.add (roff n (Nat.mul n w) (LR 0)) q0))
      (rpt w (mask w) (LR 1) k)) ||
    (Nat.blt (RI k) NR && Nat.blt (RB (RI k)) (rcnt (LR 1)) && Nat.blt (EK k) NE &&
      Nat.beq (pg w (mask w) (EP (EK k)) (pg w (mask w) BP 0)) (pg w (mask w) BP 0) &&
      Nat.beq (pg w (mask w) (EP (EK k))
          (pg w (mask w) (TR (Nat.add (roff n (Nat.mul n w) (LR 0)) q0))
            (rpt w (mask w) (LR 1) (RB (RI k)))))
        (pg w (mask w) (TR (Nat.add (roff n (Nat.mul n w) (LR 0)) q0)) (rpt w (mask w) (LR 1) k)))

end CFSG.KC.Misc.ChainTail

end
