module

public import Certificates.Kernel.Co2Smith.Cox
public import Certificates.Kernel.Co2Smith.Root
public import Certificates.Kernel.Co2Smith.WeylK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem wGen_get {g : Nat} (hg : g < 5) : glWGen.getD g #[] = unpackR 22 (wgK g) := by
  obtain ⟨-, h0, h1, -⟩ := el_eqs
  obtain ⟨e1, e2, e3, -⟩ := frame_eqs
  rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4) with rfl | rfl | rfl | rfl | rfl
  · exact e1
  · exact e2
  · exact e3
  · exact h0
  · exact h1

theorem weylChart_ok : glWeylChartOK = true := by
  unfold glWeylChartOK
  rw [charts_k, Bool.and_true, ← weyl_k]
  unfold glWeylOK weylK
  apply all_congr_mem
  intro g hg
  rw [List.mem_range] at hg
  simp only [wGen_get hg, glRootRows_eq, glConj_unpack, beq_unpack]

end CertificateChecks.KernelCo2Smith
