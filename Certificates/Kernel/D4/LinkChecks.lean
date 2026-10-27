module

public import Certificates.Kernel.D4.LinkData
public import Certificates.Kernel.D4.Tabs
public import Certificates.Kernel.D4.ChainAD
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.D4LinkK
public import Certificates.Data.Kernel.D4K
public import Certificates.Data.Kernel.BfsPin
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K
open CFSG.KC.Misc.ArrEnum CFSG.KC.D4K CFSG.KC.D4Link
open CFSG.KLie.CT (fget)

theorem gm : allN 18 (fun k => allN 64 fun t =>
    Nat.beq ((genCodes.getD k #[])[t]!) (vget (LG k) t)) = true := by quickRfl

theorem root : Nat.beq (LV 0) 1 = true := by quickRfl

@[expose] noncomputable def validSl (s : Nat) : Bool := allBlk (Nat.mul 117 s) (fun i => validK (LV i)) 117

theorem dist : CFSG.KC.BfsPin.distinctK 2457 (fun i => keyK (LV i)) LS = true := by quickRfl

theorem c0 : Nat.beq (LC 0) 1 = true := by quickRfl

theorem cK : Nat.beq (LC 21) 2457 = true := by quickRfl

@[expose] noncomputable def runSl (s : Nat) : Bool := runSlV (actK LG) 18 LV LE 117 LC s

@[expose] noncomputable def pbSl (s : Nat) : Bool :=
  allBlk (Nat.mul 117 s) (fun i => allN 18 fun k =>
    Nat.beq (pg 12 (mask 12) (LP k) i) (fget (LE i) k 12)) 117

theorem pP : allN 18 (fun k => permB 2457 12 (LP k)) = true := by quickRfl

theorem pAB : permB 2457 12 (HX.F 66) = true ∧ permB 2457 12 (HX.F 67) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem wordA : Nat.beq (HX.F 66) (cm 2457 12 (LP 2) (cm 2457 12 (LP 5)
    (cm 2457 12 (LP 10) (pidn 2457 12)))) = true := by quickRfl

theorem wordB : Nat.beq (HX.F 67) (cm 2457 12 (LP 16) (cm 2457 12 (LP 17) (cm 2457 12 (LP 7)
    (cm 2457 12 (LP 4) (cm 2457 12 (LP 10) (pidn 2457 12)))))) = true := by quickRfl

theorem siftP : allN 18 (fun k => siftOK 2457 12 CA.LR CA.TRI CA.BP 7 (LP k)) = true := by
  quickRfl

end CertificateChecks.KernelD4

end

#kss_each CertificateChecks.KernelD4.VA CertificateChecks.KernelD4.validSl 21
#kss_each CertificateChecks.KernelD4.RA CertificateChecks.KernelD4.runSl 21
#kss_each CertificateChecks.KernelD4.PB CertificateChecks.KernelD4.pbSl 21
