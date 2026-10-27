module

public import Certificates.Data.Kernel.CoreD2K.Check

public section

namespace CFSG.KS.K36K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2

@[expose] noncomputable def eqYK (n w p z v l r : Nat) : Bool :=
  bIf(allN p (fun α => allN p (fun β => bIf(Nat.beq l
    (pcomp n w (mask w) (pcomp n w (mask w) (pw n w z α) (pw n w v β)) r), false, true))),
    false, true)

@[expose] noncomputable def normYK (n w p z v m : Nat) (CT : Nat → Nat) : Bool :=
  allN m (fun l => strictB (CT l) (fun c =>
    bAnd(eqYK n w p z v (pcomp n w (mask w) c z) c, eqYK n w p z v (pcomp n w (mask w) c v) c)))

@[expose] noncomputable def centYK (n w p z v cnt : Nat) (T : Nat → Nat) : Bool :=
  allN cnt (fun i => strictB (T i) (fun t =>
    bIf(bAnd(Nat.beq (pcomp n w (mask w) t z) (pcomp n w (mask w) z t),
      Nat.beq (pcomp n w (mask w) t v) (pcomp n w (mask w) v t)),
      eqYK n w p z v t (pidn n w), true)))

@[expose] noncomputable def cntCK (n w u cnt : Nat) (T : Nat → Nat) : Nat :=
  foldN cnt (fun i c => nIf(strictB (T i) (fun t =>
    Nat.beq (pcomp n w (mask w) t u) (pcomp n w (mask w) u t)), Nat.succ c, c)) (nat_lit 0)

@[expose] noncomputable def excNK (n w p B z v m : Nat) (CT : Nat → Nat) (cnt : Nat)
    (T : Nat → Nat) : Bool :=
  bAnd(normYK n w p z v m CT, bAnd(centYK n w p z v cnt T,
    allN p (fun α => allN p (fun β => bIf(bAnd(Nat.beq α (nat_lit 0), Nat.beq β (nat_lit 0)), true,
      Nat.ble B (cntCK n w (pcomp n w (mask w) (pw n w z α) (pw n w v β)) cnt T))))))

end CFSG.KS.K36K

end
