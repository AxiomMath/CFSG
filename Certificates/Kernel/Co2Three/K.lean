module

public import Certificates.Kernel.Co2Three.Bind
public import Certificates.Kernel.Co2Pump.Bind
public import Certificates.Kernel.Misc.Perm.C2K
public import Certificates.Data.Kernel.Co2Three.DSearchM

public section

namespace CertificateChecks.KernelCo2Three

open CFSG.KC.Enum CertificateChecks.KernelMisc.Co2K CFSG.KC.Co2Three

@[expose] noncomputable def QD (j : ℕ) : ℕ := CertificateChecks.KernelCo2Pump.DMt j

@[expose] noncomputable def ED (k : ℕ) : ℕ := CertificateChecks.KernelCo2Pump.DMt (Nat.add 7 k)

@[expose] noncomputable def QDI (j : ℕ) : ℕ := HMt j

@[expose] noncomputable def GM (ρ : ℕ) : ℕ := HMt (Nat.add 3 (Nat.mul 14 ρ))

@[expose] noncomputable def GIM (ρ : ℕ) : ℕ := HMt (Nat.add 4 (Nat.mul 14 ρ))

@[expose] noncomputable def YM (ρ l : ℕ) : ℕ := HMt (Nat.add (Nat.add 5 (Nat.mul 14 ρ)) l)

@[expose] noncomputable def ZM (ρ l : ℕ) : ℕ := HMt (Nat.add (Nat.add 11 (Nat.mul 14 ρ)) l)

@[expose] noncomputable def RT (ρ : ℕ) : ℕ := f12 (HIt 0) ρ

@[expose] noncomputable def SR (ρ c : ℕ) : ℕ := f12 (HIt (Nat.add 1 ρ)) c

@[expose] noncomputable def TT (ρ i : ℕ) : ℕ := SR ρ i

@[expose] noncomputable def RFn (ρ i : ℕ) : ℕ := SR ρ (Nat.add 6 i)

@[expose] noncomputable def RSn (ρ i : ℕ) : ℕ := SR ρ (Nat.add 12 i)

@[expose] noncomputable def RKn (ρ i : ℕ) : ℕ := SR ρ (Nat.add 18 i)

@[expose] noncomputable def FTn (ρ i : ℕ) : ℕ := SR ρ (Nat.add 24 i)

@[expose] noncomputable def FKn (ρ i : ℕ) : ℕ := SR ρ (Nat.add 30 i)

@[expose] noncomputable def HH (h : ℕ) : ℕ := f12 (HIt 9) h

@[expose] noncomputable def HP (h : ℕ) : ℕ := f12 (HIt 10) h

@[expose] noncomputable def HJ (h : ℕ) : ℕ := f12 (HIt 11) h

@[expose] noncomputable def HD (h : ℕ) : ℕ := f12 (HIt 12) h

@[expose] noncomputable def CV (m : ℕ) : ℕ := f12 (HIt 13) m

@[expose] noncomputable def CC (j i : ℕ) : ℕ := f12 (HIt 14) (Nat.add (Nat.mul 4 j) i)

@[expose] noncomputable def beqB (a b : Bool) : Bool := bIf(a, b, !b)

@[expose] noncomputable def qK (QI : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (j : ℕ) : Bool :=
  Nat.beq (mmK (QD j) (QI j)) I22 && Nat.beq (mmK (QI j) (QD j)) I22 &&
    allN 4 (fun i => Nat.blt (C j i) 81) &&
    allN 81 fun k => Nat.beq (ED (linK (C j) k)) (mmK (mmK (QI j) (ED k)) (QD j))

@[expose] noncomputable def ch13636Q (j : ℕ) : Bool := qK QDI CC j

@[expose] noncomputable def gProd (T : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) I22 (fun i acc => mmK (TM i (T i)) acc) 6

@[expose] noncomputable def conjG (G GI k : ℕ) : ℕ := mmK (mmK G (ED k)) GI

@[expose] noncomputable def inB (r k : ℕ) : Bool := Nat.blt k 81 && Nat.beq (dotK r k) 0

@[expose] noncomputable def relOK (r G GI : ℕ) (RF RS RK Y : ℕ → ℕ) (l : ℕ) : Bool :=
  !(Nat.beq (RF l) 1) || (Nat.blt (RS l) l && inB r (RK l) && Nat.beq (Y l) (conjG G GI (RK l)) &&
    Nat.beq (vmK (VG (BS (RS l))) (Y l)) (VG (BS l)))

@[expose] noncomputable def fixOK (r G GI : ℕ) (FT FK Z : ℕ → ℕ) (l : ℕ) : Bool :=
  !(Nat.beq (FT l) 1) || (inB r (FK l) && Nat.beq (Z l) (conjG G GI (FK l)) &&
    Nat.beq (vmK (VG (BS l)) (Z l)) (VG (BS l)))

@[expose] noncomputable def rootK (r G GI : ℕ) (T RF RS RK Y FT FK Z : ℕ → ℕ) : Bool :=
  Nat.blt r 81 && !(Nat.beq r 0) && allN 6 (fun i => Nat.blt (T i) (mL i)) &&
    Nat.beq G (gProd T) && Nat.beq (mmK G GI) I22 && Nat.beq (mmK GI G) I22 &&
    allN 6 (fun l => relOK r G GI RF RS RK Y l && fixOK r G GI FT FK Z l)

@[expose] noncomputable def ch13636R (ρ : ℕ) : Bool :=
  rootK (RT ρ) (GM ρ) (GIM ρ) (TT ρ) (RFn ρ) (RSn ρ) (RKn ρ) (YM ρ) (FTn ρ) (FKn ρ) (ZM ρ)

@[expose] noncomputable def forestK (H P J D : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (h : ℕ) : Bool :=
  Nat.blt (H h) 81 && Nat.blt (J h) 4 &&
    bIf(Nat.beq (J h) 3, Nat.blt (P h) 8 && Nat.beq (RT (P h)) (H h),
      Nat.blt (P h) 40 && Nat.blt (D (P h)) (D h) &&
        allN 81 fun k => beqB (Nat.beq (dotK (H (P h)) k) 0)
          (Nat.beq (dotK (H h) (linK (C (J h)) k)) 0))

@[expose] noncomputable def ch13636F (j : ℕ) : Bool :=
  allN 10 fun t => forestK HH HP HJ HD CC (Nat.add (Nat.mul 10 j) t)

@[expose] noncomputable def coverK (V : ℕ → ℕ) (m : ℕ) : Bool :=
  Nat.blt (V m) 40 && allN 81 fun k => beqB (Nat.beq (dotK m k) 0) (Nat.beq (dotK (HH (V m)) k) 0)

@[expose] noncomputable def ch13636C (j : ℕ) : Bool :=
  allN 20 fun t => coverK CV (Nat.add (Nat.add (Nat.mul 20 j) t) 1)

@[expose] noncomputable def hypG (RF RS Y FT Z : ℕ → ℕ) : ℕ :=
  dsearchM vmK mmK VG BS LK (fun i => Nat.beq (RF i) 1) (fun i => Nat.beq (FT i) 1) RS Y
    (fun i u => bIf(Nat.beq (FT i) 1, Nat.beq (vmK u (Z i)) u, true)) (fun _ => true)
    mL PT PO TM TIM 6 0 I22 I22

@[expose] noncomputable def hypS (ρ : ℕ) : ℕ := hypG (RFn ρ) (RSn ρ) (YM ρ) (FTn ρ) (ZM ρ)

@[expose] noncomputable def ch13636Hyp (ρ : ℕ) : Bool := Nat.ble (hypS ρ) 162

end CertificateChecks.KernelCo2Three

end
