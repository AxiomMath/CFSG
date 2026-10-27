module

public import Certificates.Kernel.Co2Three.QBind
public import Certificates.Kernel.Co2Three.K
public import Certificates.Data.Kernel.MonsterB.BfsReplay

public section

namespace CertificateChecks.KernelCo2Three

open CFSG.KC.Enum CertificateChecks.KernelMisc.Co2K CFSG.RankThree.Native.F2

@[expose] noncomputable def QP (i : ℕ) : ℕ := QMt i

@[expose] noncomputable def HM (i : ℕ) : ℕ := QMt (Nat.add 729 i)

@[expose] noncomputable def HMI (i : ℕ) : ℕ := QMt (Nat.add 745 i)

@[expose] noncomputable def QE (i k : ℕ) : ℕ := f12 (QIt 0) (Nat.add (Nat.mul 3 i) k)

@[expose] noncomputable def QR (i : ℕ) : ℕ := f12 (QIt 1) i

@[expose] noncomputable def QL (i : ℕ) : ℕ := f12 (QIt 2) i

@[expose] noncomputable def QSO (j : ℕ) : ℕ := f12 (QIt 3) j

@[expose] noncomputable def QSOI (j : ℕ) : ℕ := f12 (QIt 4) j

@[expose] noncomputable def FKd (i : ℕ) : ℕ := f12 (QIt 5) i

@[expose] noncomputable def FH (i : ℕ) : ℕ := f12 (QIt 6) i

@[expose] noncomputable def FE (i : ℕ) : ℕ := f12 (QIt 7) i

@[expose] noncomputable def HT (i l : ℕ) : ℕ := f12 (QIt 8) (Nat.add (Nat.mul 6 i) l)

@[expose] noncomputable def qKey (PM : ℕ → ℕ) (i : ℕ) : ℕ := keyM vmK 2300 VG LK [2, 2007] PM i

@[expose] noncomputable def qPtsK (PM : ℕ → ℕ) (E : ℕ → ℕ → ℕ) (R L : ℕ → ℕ) (lo cnt : ℕ) :
    Bool :=
  allN cnt fun t => pointM mmK 3 729 QD PM E R L (Nat.add lo t)

@[expose] noncomputable def qKeysK (PM SO SOI : ℕ → ℕ) (lo cnt : ℕ) : Bool :=
  allN cnt fun t => (fun j => Nat.blt (SO j) 729 && Nat.beq (SOI (SO j)) j &&
    (!(Nat.blt (Nat.add j 1) 729) || Nat.blt (qKey PM (SO j)) (qKey PM (SO (Nat.add j 1)))))
    (Nat.add lo t)

@[expose] noncomputable def ch13636QP (c : ℕ) : Bool := qPtsK QP QE QR QL (Nat.mul 81 c) 81

@[expose] noncomputable def ch13636QK (c : ℕ) : Bool := qKeysK QP QSO QSOI (Nat.mul 81 c) 81

@[expose] noncomputable def qRootK (PM : ℕ → ℕ) (E : ℕ → ℕ → ℕ) : Bool :=
  Nat.beq (PM 0) I22 && CFSG.KC.Bfs.replayOK E 3 729

@[expose] noncomputable def ch13636QR (_ : ℕ) : Bool := qRootK QP QE

@[expose] noncomputable def hK (T : ℕ → ℕ) (H HI : ℕ) : Bool :=
  allN 6 (fun l => Nat.blt (T l) (mL l)) && Nat.beq H (gProd T) &&
    Nat.beq (mmK H HI) I22 && Nat.beq (mmK HI H) I22 &&
    siftM vmK mmK I22 2300 VG BS LK mL PO TIM 6 0 H

@[expose] noncomputable def ch13636H (i : ℕ) : Bool := hK (HT i) (HM i) (HMI i)

@[expose] noncomputable def ch13636S (j : ℕ) : Bool :=
  siftM vmK mmK I22 2300 VG BS LK mL PO TIM 6 0 (CertificateChecks.KernelCo2Pump.DMt j)

@[expose] noncomputable def dK (DD E : ℕ → ℕ) : Bool :=
  allN 4 (fun i => Nat.beq (pwK (DD i) 3) I22) &&
    allN 4 (fun i => allN 4 fun j => comm (DD i) (DD j)) &&
    allN 81 fun k => allN 81 fun k' => Nat.beq k k' || !(Nat.beq (E k) (E k'))

@[expose] noncomputable def ch13636D (_ : ℕ) : Bool :=
  dK (fun i => CertificateChecks.KernelCo2Pump.DMt (Nat.add 3 i)) ED

@[expose] noncomputable def fusK (H HI : ℕ → ℕ) (P κ i k : ℕ) : Bool :=
  bIf(Nat.beq κ 0, !(Nat.beq (pwK P 3) I22) || Nat.beq P I22,
    Nat.blt k 81 && bIf(Nat.beq κ 1, Nat.beq (ED k) P,
      Nat.blt i 16 && Nat.beq (ED k) (mmK (mmK (HI i) P) (H i))))

@[expose] noncomputable def ch13636Fus (c : ℕ) : Bool :=
  allN 81 fun t => (fun j => fusK HM HMI (QP j) (FKd j) (FH j) (FE j)) (Nat.add (Nat.mul 81 c) t)

end CertificateChecks.KernelCo2Three

end
