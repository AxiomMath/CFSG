module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KS.SchreierFam

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def wordK (n w : Nat) (G : Nat → Nat) (l : List Nat) : Nat :=
  l.foldl (fun x i => pcomp n w (mask w) x (G i)) (pidn n w)

@[expose] noncomputable def cjK (n w W C : Nat) : Nat :=
  pcomp n w (mask w) W (pcomp n w (mask w) C (pinvS n w (mask w) W))

@[expose] noncomputable def invoNe (n w R X : Nat) : Bool :=
  bAnd(Nat.beq (pcomp n w (mask w) X X) (pidn n w),
    bIf(Nat.beq X (pidn n w), false, bIf(Nat.beq X R, false, true)))

@[expose] noncomputable def cqK (n w R : Nat) (G : Nat → Nat) (L : List (List Nat)) (C : Nat) :
    Bool :=
  bIf(Nat.beq (pcomp n w (mask w) C C) R,
    L.any fun l => invoNe n w R (pcomp n w (mask w) C (cjK n w (wordK n w G l) C)), true)

end CFSG.KS.SchreierFam
