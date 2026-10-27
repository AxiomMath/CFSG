module

public import Certificates.Data.TitsAschbacherSecFour
public import Certificates.Kernel.EvenBN.Bind
public import Certificates.Kernel.SporSch.Tits.Inv2266
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27014

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch.TitsCentral CertificateChecks.KernelSporSch.TitsInv
open CertificateChecks.KernelEvenBN
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherSecFour

set_option simprocs false in
theorem tits_sec_four_check_0 : tCommCheck = true := by
  obtain ⟨ha, ca⟩ := chain_gen bindsN canN (w := commWordA) (by decide)
  obtain ⟨hb, cb⟩ := chain_gen bindsN canN (w := commWordB) (by decide)
  unfold tCommCheck nArr
  rw [ha, hb, t_eq]
  simp (config := { maxDischargeDepth := 12 }) only [commA, cmpU, cmpC, eqU, ca, cb, cT]
  quickRfl

end CertificateChecks.Batch27014

namespace Certificates

open CertificateChecks

theorem certificate27014 : Certificates.TitsAschbacherSecFour.tCommCheck = true := by
  exact CertificateChecks.Batch27014.tits_sec_four_check_0

end Certificates
