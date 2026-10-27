module

public import Certificates.Data.Kernel.SmithEKCd

public section

namespace CFSG.SmithE.K

open CFSG.KC.Misc.O73

@[expose] noncomputable def fpScale (l c : Nat) : Nat := cdMapC (fun _ x => cdMul l x) c

@[expose] noncomputable def fpWts (WT : List Nat) : List Nat → List Nat :=
  fun PI => List.rec (motive := fun _ => List Nat) []
    (fun i _ ih => WT.getD i 0 :: ih) PI

@[expose] noncomputable def fpPairsK (TP : Nat → Nat) (W : List Nat) (L a : Nat)
    (PL : List (List Nat)) (PM PI PJ : List Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k acc => acc && cdPlK TP W L a PL PM (PI.getD k 0) (PJ.getD k 0)) 20

@[expose] noncomputable def fpUnitK (WT PI UM : List Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun t acc => acc && Nat.beq (cdSel (fpWts WT PI) (UM.getD t 0)) (Nat.pow 2 t)) 20

@[expose] noncomputable def fpBsK (WT PI PJ BS BM : List Nat) : Bool :=
  Nat.ble (lenK BS) 8 &&
    Nat.rec (motive := fun _ => Bool) true
      (fun k acc => acc && Nat.beq (cdSel BS (BM.getD k 0))
        (Nat.xor (WT.getD (PJ.getD k 0) 0) (WT.getD (PI.getD k 0) 0))) 20

@[expose] noncomputable def fpFixK (TP : Nat → Nat) (W : List Nat) (L a M : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun x acc => acc && (bif Nat.beq (cdImg TP W L a x) x then bitK M x else true)) 693

@[expose] noncomputable def fpAllK (TP : Nat → Nat) (W : List Nat) (L a : Nat) : List Nat → Bool :=
  fun FX => List.rec (motive := fun _ => Bool) true
    (fun y ys ih => Nat.blt y 693 && Nat.beq (cdImg TP W L a y) y && !memK y ys && ih) FX

@[expose] noncomputable def fpCodeK (PC FX FC : List Nat) : Bool :=
  Nat.beq (lenK FC) (lenK FX) &&
    Nat.rec (motive := fun _ => Bool) true
      (fun k acc => acc && Nat.beq (FC.getD k 0) (PC.getD (FX.getD k 0) 0)) (lenK FX)

@[expose] noncomputable def fpTreeK (TP : Nat → Nat) (FX FE : List Nat) : Bool :=
  Nat.beq (Nat.succ (lenK FE)) (lenK FX) &&
    Nat.rec (motive := fun _ => Bool) true
      (fun k acc => acc && Nat.blt (Nat.mod (FE.getD k 0) 64) (lenK FX) &&
        Nat.ble (Nat.div (FE.getD k 0) 64) k &&
        Nat.beq (at' 10 (TP (FX.getD (Nat.mod (FE.getD k 0) 64) 0))
          (FX.getD (Nat.div (FE.getD k 0) 64) 0)) (FX.getD (Nat.succ k) 0)) (lenK FE)

@[expose] noncomputable def fpLineK (FC FL : List Nat) : Bool :=
  Nat.beq (Nat.succ (lenK FL)) (lenK FC) &&
    Nat.rec (motive := fun _ => Bool) true
      (fun k acc => acc &&
        Nat.ble (Nat.mod (FL.getD k 0) 64) k &&
        Nat.blt (Nat.mod (Nat.div (FL.getD k 0) 64) 64) (lenK FC) &&
        Nat.blt 0 (Nat.mod (Nat.div (FL.getD k 0) 4096) 4) &&
        Nat.blt 0 (Nat.div (FL.getD k 0) 16384) && Nat.blt (Nat.div (FL.getD k 0) 16384) 4 &&
        Nat.beq (FC.getD (Nat.mod (Nat.div (FL.getD k 0) 64) 64) 0)
          (Nat.xor (fpScale (Nat.mod (Nat.div (FL.getD k 0) 4096) 4) (FC.getD (Nat.mod (FL.getD k 0) 64) 0))
            (fpScale (Nat.div (FL.getD k 0) 16384) (FC.getD (Nat.succ k) 0)))) (lenK FL)

@[expose] noncomputable def fpComb (FC : List Nat) : List Nat → Nat :=
  fun S => List.rec (motive := fun _ => Nat) 0
    (fun e _ ih => Nat.xor (fpScale (Nat.div e 64) (FC.getD (Nat.mod e 64) 0)) ih) S

@[expose] noncomputable def fpSpanK (FC : List Nat) (SP : List (List Nat)) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun t acc => acc && Nat.beq (fpComb FC (SP.getD t [])) (Nat.pow 4 t) &&
      List.rec (motive := fun _ => Bool) true
        (fun e _ ih => Nat.blt (Nat.mod e 64) (lenK FC) && Nat.blt (Nat.div e 64) 4 && ih)
        (SP.getD t [])) 6

@[expose] noncomputable def fpRepK (TP : Nat → Nat) (W : List Nat) (L a : Nat)
    (PL : List (List Nat)) (PM WT PC PI PJ UM BS BM FX FC FE FL : List Nat)
    (SP : List (List Nat)) : Bool :=
  Nat.beq (lenK PI) 20 && Nat.beq (lenK PJ) 20 &&
    fpPairsK TP W L a PL PM PI PJ && fpUnitK WT PI UM && fpBsK WT PI PJ BS BM &&
    fpFixK TP W L a (maskK FX) && fpAllK TP W L a FX && Nat.beq (Nat.mod (lenK FX) 2) 1 &&
    Nat.ble (lenK FX) 64 && fpCodeK PC FX FC && fpTreeK TP FX FE && fpLineK FC FL &&
    fpSpanK FC SP

end CFSG.SmithE.K
