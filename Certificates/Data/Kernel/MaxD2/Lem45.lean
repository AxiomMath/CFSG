module

public import Certificates.Data.Kernel.MaxD2.Check

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Row CFSG.KS.PEnum

@[expose] noncomputable def wcK (n w U W k : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) (pw n w U k) W) (pw n w U (Nat.sub 5 k))

@[expose] noncomputable def gSel (kN : Nat) (NG NGI : Nat → Nat) (g : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (NGI (Nat.sub g kN)) (NG g) (Nat.blt g kN)

@[expose] noncomputable def giSel (kN : Nat) (NG NGI : Nat → Nat) (g : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (NG (Nat.sub g kN)) (NGI g) (Nat.blt g kN)

@[expose] noncomputable def stepK (n w rcnt kN : Nat) (NG NGI RT IX : Nat → Nat) (k p g : Nat) :
    Bool :=
  bAnd(Nat.blt p (Nat.succ k), bAnd(Nat.blt g (Nat.mul 2 kN), bAnd(Nat.blt (IX (Nat.succ k)) rcnt,
    Nat.beq (RT (IX (Nat.succ k))) (pcomp n w (mask w)
      (pcomp n w (mask w) (gSel kN NG NGI g) (RT (IX p))) (giSel kN NG NGI g)))))

@[expose] noncomputable def treeK (n w rcnt kN : Nat) (NG NGI RT IX : Nat → Nat)
    (tr : List (Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun pg _ ih k => strictB k (fun k =>
      Prod.rec (motive := fun _ => Bool)
        (fun p g => bAnd(stepK n w rcnt kN NG NGI RT IX k p g, ih (Nat.succ k))) pg)) tr

@[expose] noncomputable def covK (nz m : Nat) (ZP ZX IX CV : Nat → Nat) (i : Nat) : Bool :=
  bIf(bAnd(Nat.blt 0 (ZX i), bAnd(Nat.ble (ZX i) nz, Nat.beq (ZP (Nat.sub (ZX i) 1)) i)), true,
    bAnd(Nat.blt (CV i) m, Nat.beq (IX (CV i)) i))

end CFSG.KS.MaxD2
