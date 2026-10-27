module

public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.ListBridge

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (anyN)

@[expose] noncomputable def pwordK (n w : Nat) (P : Nat → Nat) (wd : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w)
    (fun z _ acc => pcomp n w (mask w) (P (Nat.sub (Int.toNat z) 1)) acc) wd

@[expose] def posW (ng : Nat) (wd : List Int) : Bool :=
  wd.all fun z => decide (0 < z) && decide (z.toNat ≤ ng)

@[expose] noncomputable def psqK (n w k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ acc => strictN acc fun a => pcomp n w (mask w) a a) k

@[expose] noncomputable def inK (N : Nat) (T : Nat → Nat) (x : Nat) : Bool :=
  anyN N fun j => Nat.beq (T j) x

@[expose] noncomputable def powK (n w k N : Nat) (T : Nat → Nat) : Bool :=
  allN N fun i => Nat.beq (psqK n w k (T i)) (pidn n w)

@[expose] noncomputable def normK (n w N : Nat) (T : Nat → Nat) (g : Nat) : Bool :=
  allN N fun i =>
    bAnd(inK N T (pcomp n w (mask w) (pcomp n w (mask w) g (T i)) (pinvS n w (mask w) g)),
      inK N T (pcomp n w (mask w) (pcomp n w (mask w) (pinvS n w (mask w) g) (T i)) g))

@[expose] noncomputable def selfK (n w NK : Nat) (TK : Nat → Nat) (ng : Nat) (G : Nat → Nat)
    (NU : Nat) (TU : Nat → Nat) : Bool :=
  allN NK fun i => strictB (TK i) fun t =>
    bIf(allN ng fun k => Nat.beq (pcomp n w (mask w) t (G k)) (pcomp n w (mask w) (G k) t),
      inK NU TU t, true)

end CFSG.KC.ListBridge

end
