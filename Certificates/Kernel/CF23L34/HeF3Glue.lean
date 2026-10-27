module

public import Certificates.Kernel.CF23L34.HeF3
public import Certificates.Kernel.CF23L34.HeGSLGlue
public import Certificates.Data.GrSLitHeF3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeF3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermTool
open CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.ComponentClassification.GrSLit.HeGS
open Certificates.GrSLitHeZStar Certificates.GrSLitHeF3
open CertificateChecks.KernelLC.HeFix CertificateChecks.KernelLC.HeGS36
open CertificateChecks.KernelLC.HeGSL

theorem avoid_spec {p : Nat} (hp : cn p = true) (h : avoid p = true) :
    unpack 8330 14 p ≠ idTab 8330 ∧ unpack 8330 14 p ≠ heGen 0 ∧ unpack 8330 14 p ≠ heZUTab ∧
      unpack 8330 14 p ≠ heZT0UTab := by
  have ku := kw (w := heGSComm2 heGSUComm) (by decide)
  have cT : cn (pc (HG.F 0) (K (heGSComm2 heGSUComm))) = true := cnpc cnG.1 ku.2
  have eU : heZUTab = unpack 8330 14 (K (heGSComm2 heGSUComm)) := by
    unfold heZUTab
    exact ku.1
  have eT : heZT0UTab = unpack 8330 14 (pc (HG.F 0) (K (heGSComm2 heGSUComm))) := by
    unfold heZT0UTab
    rw [eU, heGen_eq (k := 0) (by decide), cmp cnG.1 ku.2]
  unfold avoid at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [hidT, heGen_eq (k := 0) (by decide), eU, eT]
  exact ⟨ne_of hp hid h1, ne_of hp cnG.1 h2, ne_of hp ku.2 h3, ne_of hp cT h4⟩

theorem check22705 :
    comp 8330 heF3W1Tab heF3W1Tab = idTab 8330 ∧ comp 8330 heF3W2Tab heF3W2Tab = idTab 8330 ∧
      heF3W12Tab = comp 8330 heF3W2Tab heF3W1Tab ∧
      heF3W1Tab ≠ idTab 8330 ∧ heF3W1Tab ≠ heGen 0 ∧ heF3W1Tab ≠ heZUTab ∧
      heF3W1Tab ≠ heZT0UTab ∧
      heF3W2Tab ≠ idTab 8330 ∧ heF3W2Tab ≠ heGen 0 ∧ heF3W2Tab ≠ heZUTab ∧
      heF3W2Tab ≠ heZT0UTab ∧
      heF3W12Tab ≠ idTab 8330 ∧ heF3W12Tab ≠ heGen 0 ∧ heF3W12Tab ≠ heZUTab ∧
      heF3W12Tab ≠ heZT0UTab := by
  have ka := kw (w := heGSEW [2, 4, 2, 4]) (by decide)
  have kb := kw (w := heGSEW [1]) (by decide)
  have cab := cnpc ka.2 kb.2
  have h := ch22705
  unfold f3OK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨haa, hbb, hab, va, vb, vab⟩ := h
  have e1 : heF3W1Tab = unpack 8330 14 (K (heGSEW [2, 4, 2, 4])) := by
    unfold heF3W1Tab
    exact ka.1
  have e2 : heF3W2Tab = unpack 8330 14 (K (heGSEW [1])) := by
    unfold heF3W2Tab
    exact kb.1
  have e12 : heF3W12Tab = unpack 8330 14 (pc (K (heGSEW [2, 4, 2, 4])) (K (heGSEW [1]))) := by
    unfold heF3W12Tab
    rw [e1, e2, cmp ka.2 kb.2]
  obtain ⟨a1, a2, a3, a4⟩ := avoid_spec ka.2 va
  obtain ⟨b1, b2, b3, b4⟩ := avoid_spec kb.2 vb
  obtain ⟨c1, c2, c3, c4⟩ := avoid_spec cab vab
  rw [← e1] at a1 a2 a3 a4
  rw [← e2] at b1 b2 b3 b4
  rw [← e12] at c1 c2 c3 c4
  refine ⟨?_, ?_, ?_, a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4⟩
  · rw [e1, cmp ka.2 ka.2, Nat.eq_of_beq_eq_true haa, hidT]
  · rw [e2, cmp kb.2 kb.2, Nat.eq_of_beq_eq_true hbb, hidT]
  · rw [e12, e1, e2, cmp kb.2 ka.2, Nat.eq_of_beq_eq_true hab]

end CertificateChecks.KernelLC.HeF3

end
