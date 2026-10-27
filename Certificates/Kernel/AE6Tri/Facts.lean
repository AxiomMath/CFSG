module

public import Certificates.Data.Kernel.AE6Tri.Defs
public import Certificates.Kernel.AE6Tri.Data
public import Certificates.Kernel.AE6Tri.DataB
public import Certificates.Kernel.AE6Tri.DataC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6STri

public section

namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.AE6Tri CFSG.KD.AE6Tri CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

theorem vl_iff : ∀ (k : Fin 3) (i : Fin 8), i ∈ ae6VertexLetters k ↔ i.val ∈ vl.getD k [] := by
  decide

theorem el_iff : ∀ i : Fin 8, i ∈ ae6EdgeLetters 0 1 ↔ i.val ∈ el := by decide

theorem mask_iff : ∀ i : Fin 8, (bit 93 i.val = true ↔ i ∈ ae6MLetters) ∧
    (bit 253 i.val = true ↔ i ∈ ae6VertexLetters 0) ∧ (bit 125 i.val = true ↔ i ∈ ae6EdgeLetters 0 1) := by
  decide

theorem qzJ_lt : ∀ x < qw.length, ∀ y < qw.length, at2 qzJ 0 y x < (qg.getD x []).length := by
  decide

theorem kU_len : kU.length = 3 := by decide

theorem shapes : qw.length = 4 ∧ (qw.map List.length = qg.map List.length) ∧ delta.length = 3 ∧
    dg.length = 3 ∧ ml.length = 5 ∧ el.length = 6 ∧ tgW.length = 6 := by decide

end CertificateChecks.KernelAE6Tri

end
