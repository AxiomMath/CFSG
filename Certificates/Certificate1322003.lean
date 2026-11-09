module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3MathieuData
import all CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3MathieuData
import CFSG.Certificates.Kernel.PermCent.CVSound

public section

namespace CertificateChecks.Batch1322003

open CFSG.Certificates.Kernel.PkCV CFSG.M23

private instance small22 : CFSG.Certificates.Kernel.PkCV.Small 22 := ⟨by decide⟩
private instance small24 : CFSG.Certificates.Kernel.PkCV.Small 24 := ⟨by decide⟩

private theorem evalGroupWord_ev' {k m : ℕ} [CFSG.Certificates.Kernel.PkCV.Small m] (S : Fin k → CV m) (w : List (Fin k × Bool)) :
    evalGroupWord (fun i => ev (S i)) w = ev (evalGroupWord S w) := by
  induction w with
  | nil => exact one_eq_ev
  | cons a w ih =>
    obtain ⟨i, b⟩ := a
    cases b
    · show ev (S i) * evalGroupWord (fun i => ev (S i)) w = ev (S i * evalGroupWord S w)
      rw [ih, ev_mul']
    · show (ev (S i))⁻¹ * evalGroupWord (fun i => ev (S i)) w = ev ((S i)⁻¹ * evalGroupWord S w)
      rw [ih, ev_inv', ev_mul']

private theorem ev_cOf_fun {k m : ℕ} [CFSG.Certificates.Kernel.PkCV.Small m] (S : Fin k → Equiv.Perm (Fin m)) :
    (fun i => ev (cOf (S i))) = S :=
  funext fun i => ev_cOf (S i)

end CertificateChecks.Batch1322003

namespace Certificates

open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.Mathieu

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.Mathieu CFSG.Certificates.Kernel.PkCV
  CertificateChecks.Batch1322003 in
theorem certificate1322003 : M24Facts ∧ M22Facts := by
  unfold M24Facts M22Facts
  rw [← ev_cOf_fun m24S, ← ev_cOf_fun m24GS1, ← ev_cOf_fun m24GS2, ← ev_cOf m24X, ← ev_cOf m24Y,
    ← ev_cOf m24Z, ← ev_cOf m24G11, ← ev_cOf m24G12, ← ev_cOf m24G13, ← ev_cOf m24G21,
    ← ev_cOf m24G22, ← ev_cOf m24G23, ← ev_cOf m24W2, ← ev_cOf m24W4, ← ev_cOf m24A,
    ← ev_cOf m24B, ← ev_cOf_fun m22S, ← ev_cOf_fun m22GS, ← ev_cOf m22U, ← ev_cOf m22V,
    ← ev_cOf m22C1, ← ev_cOf m22C2, ← ev_cOf m22C3, ← ev_cOf m22A, ← ev_cOf m22B]
  simp only [evalGroupWord_ev', ev_mul', ev_inv', ev_pow', one_eq_ev, ev_eq_iff, ne_eq]
  decide +kernel

end Certificates
