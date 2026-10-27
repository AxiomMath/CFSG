
module

public import Certificates.Data.GrSLitL34Sec5SWIsoCheck
import Certificates.Kernel.L34W.TypesGlue
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real in
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso in
theorem certificate22237 :
    (∀ K : AddSubgroup (ZMod 4 × ZMod 4), ∃ kb ∈ kbList, ∀ i j : ZMod 4,
      inKB kb i j = true ↔ (i, j) ∈ K) ∧
    (∀ t i : ℕ, typeOf t i < 3 → ∃ t' < 64, ∃ j < 36,
      wordPerm (tg t') * repPerm j * (wordPerm (tg t) * repPerm i) *
          (wordPerm (tg t') * repPerm j)⁻¹ =
        if typeOf t i = 0 then CFSG.ComponentClassification.PSL3Four.r₂
        else if typeOf t i = 1 then CFSG.ComponentClassification.PSL3Four.r₃
        else CFSG.ComponentClassification.PSL3Four.r₄) ∧
    (∀ t < 64, ∀ i < 36, repInS.contains i = false →
      wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) = 1 → typeOf t i < 3) ∧
    (∀ t < 64, ∀ i < 36, ∀ t' < 64, ∀ i' < 36, repInS.contains i = false →
      repInS.contains i' = false →
      wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) = 1 →
      wordPerm (tg t') * repPerm i' * (wordPerm (tg t') * repPerm i') = 1 →
      wordPerm (tg t) * repPerm i * (wordPerm (tg t') * repPerm i') =
        wordPerm (tg t') * repPerm i' * (wordPerm (tg t) * repPerm i) →
      wordPerm (tg t) * repPerm i * (wordPerm (tg t') * repPerm i') ∉
        CFSG.ComponentClassification.PSL3Four.S →
      typeOf t i ≠ typeOf t' i') :=
  ⟨KernelL34W.kclass_spec, fun _ _ h => (KernelL34W.types_spec h).2.2,
    fun _ ht _ hi hS h2 => KernelL34W.outer_spec ht hi hS h2,
    fun _ ht _ hi _ ht' _ hi' hS hS' h2 h2' hc hn =>
      KernelL34W.pairs_spec ht hi ht' hi' hS hS' h2 h2' hc hn⟩

end Certificates
