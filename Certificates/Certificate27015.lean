module

public import Certificates.Data.TitsAschbacherSecFour
public import Certificates.Kernel.EvenBN.Bind
public import Certificates.Kernel.SporSch.Tits.Inv2266
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27015

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch.TitsCommon CertificateChecks.KernelSporSch.TitsCentral
open CertificateChecks.KernelSporSch.TitsInv CertificateChecks.KernelEvenBN
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherSecFour

theorem nW (w : List Nat) (hw : ∀ j ∈ w, j < 10) :
    nArr w = unpack 1755 11 (wP TitsN.S w) ∧
      canonK 1755 11 (mask 11) (1755 * 11) (wP TitsN.S w) = true :=
  chain_gen bindsN canN hw

set_option simprocs false in
theorem tits_sec_four_check_0 : structCheck = true := by
  obtain ⟨h1, c1⟩ := nW u1Word (by decide)
  obtain ⟨h2, c2⟩ := nW u2Word (by decide)
  obtain ⟨hy, cy⟩ := nW yWord (by decide)
  obtain ⟨he, ce⟩ := nW eWord (by decide)
  obtain ⟨hf1, cf1⟩ := nW [0] (by decide)
  obtain ⟨hf2, cf2⟩ := nW [0, 1] (by decide)
  obtain ⟨hf3, cf3⟩ := nW [1] (by decide)
  obtain ⟨hq1, cq1⟩ := nW [2, 3, 3, 0, 2, 1] (by decide)
  obtain ⟨hq2, cq2⟩ := nW [0, 2, 1, 3, 0, 3, 2] (by decide)
  obtain ⟨hq3, cq3⟩ := nW [2, 0, 1, 1, 2, 3, 3] (by decide)
  unfold structCheck uSharp u3A qArrs u1A u2A yA eA
  simp only [fWords, qWords, List.zip_cons_cons, List.zip_nil_left, List.all_cons, List.all_nil,
    List.map_cons, List.map_nil]
  rw [h1, h2, hy, he, hf1, hf2, hf3, hq1, hq2, hq3, t_eq, z_eq, CertificateChecks.KernelSporSch.TitsCentral.id_eq]
  simp (config := { maxDischargeDepth := 12 }) only [commA, cmpU, cmpC, eqU, powU, powC, c1, c2, cy,
    ce, cf1, cf2, cf3, cq1, cq2, cq3, cT, canonZ, canId]
  quickRfl

end CertificateChecks.Batch27015

namespace Certificates

open CertificateChecks

theorem certificate27015 : Certificates.TitsAschbacherSecFour.structCheck = true := by
  exact CertificateChecks.Batch27015.tits_sec_four_check_0

end Certificates
