module

public import Certificates.Kernel.Co2.Join
public import Certificates.Kernel.Co2.Intro
public import Certificates.Data.Kernel.HSKill
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.T_Sel
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.B_Sel
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.C_Sel
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.X2_Sel
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.T
import Certificates.Kernel.LceSTab.Chain
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.B_W_0
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.C_W_0
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.C_L
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.X2_W_0

public section

namespace CertificateChecks.KernelHS

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CertificateChecks.KernelCo2

theorem runLab_append (WT LB LETs : Nat → Nat) (Hs : Nat) :
    ∀ l1 l2 x, HSK.runLab WT LB LETs Hs (List.append l1 l2) x =
      HSK.runLab WT LB LETs Hs l2 (HSK.runLab WT LB LETs Hs l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (HSK.labChunk WT LB LETs Hs C x) (HSK.runLab WT LB LETs Hs (List.append l1 l2)) =
      HSK.runLab WT LB LETs Hs l2
        (strictN (HSK.labChunk WT LB LETs Hs C x) (HSK.runLab WT LB LETs Hs l1))
    rw [strictN_eq, strictN_eq, runLab_append WT LB LETs Hs l1 l2]

open CFSG.KC.LceSeg in
theorem Tfacts : Nat.beq (runFacts CFSG.KD.HSKT.blk CFSG.KD.HSKT.selWT CFSG.KD.HSKT.INV
    CFSG.KD.HSKT.nC (nat_lit 4) (seg CFSG.KD.HSKT.JF
      (Nat.sub (CFSG.KD.HSKT.loF 23) (CFSG.KD.HSKT.loF 0)) (CFSG.KD.HSKT.loF 0))
    (CFSG.KD.HSKT.accF 0)) (CFSG.KD.HSKT.accF 23) = true :=
  facts_chain _ _ _ _ _ _ _ _ 23 CFSG.KD.HSKT.okW_all

open CFSG.KC.LceSeg in
theorem Tcover : Nat.beq (runCover CFSG.KD.HSKT.blk CFSG.KD.HSKT.LVs (nat_lit 42324)
    (nat_lit 4) (seg CFSG.KD.HSKT.JV
      (Nat.sub (CFSG.KD.HSKT.loC 5) (CFSG.KD.HSKT.loC 0)) (CFSG.KD.HSKT.loC 0))
    (CFSG.KD.HSKT.accC 0)) (CFSG.KD.HSKT.accC 5) = true :=
  cover_chain _ _ _ _ _ _ _ 5 CFSG.KD.HSKT.okC_all
#kc_join_range Bfacts CertificateChecks.KernelCo2.runFacts_append CFSG.KD.HSKB "sW" 0 29
#kc_join_range Cfacts CertificateChecks.KernelCo2.runFacts_append CFSG.KD.HSKC "sW" 0 1
#kc_join_range Clab CertificateChecks.KernelHS.runLab_append CFSG.KD.HSKC "sL" 0 1
#kc_join_range X2facts CertificateChecks.KernelCo2.runFacts_append CFSG.KD.HSKX2 "sW" 0 3

theorem coneOk_intro {blk WT RT ST LB LETs : Nat → Nat}
    {INV INV8 L nC nf m Hs K S0 S1 T0 T1 : Nat} {Cs : List Nat}
    (h1 : wordsOK WT RT ST INV INV8 m Hs = true) (h2 : invOK INV INV8 L = true)
    (h3 : Nat.ble nC (nat_lit 1048576) = true) (h4 : Nat.blt nf (nat_lit 4294967296) = true)
    (h5 : Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)) = true) (h6 : Nat.beq S1 (mkS nf nC) = true)
    (h7 : Nat.beq T0 (nat_lit 1) = true) (h8 : Nat.beq T1 (Nat.succ nf) = true)
    (h9 : HSK.hintsLt WT m K Hs = true)
    (h10 : Nat.beq (CFSG.KC.LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1) = true)
    (h11 : Nat.beq (runFacts blk WT INV nC L Cs S0) S1 = true)
    (h12 : Nat.beq (HSK.runLab WT LB LETs Hs Cs T0) T1 = true) :
    CFSG.Certificates.HSKill.coneOk blk WT RT ST LB LETs INV INV8 L nC nf m Hs K S0 S1 T0 T1 Cs =
      true := by
  unfold CFSG.Certificates.HSKill.coneOk
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  rfl

end CertificateChecks.KernelHS

end
