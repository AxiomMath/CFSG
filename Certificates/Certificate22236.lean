
module

public import Certificates.Data.GrSLitL34Sec5SWIsoCheck
import Certificates.Kernel.L34W.DGlue
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real in
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso in
theorem certificate22236 : ∀ kb ∈ kbList, ∀ t < 64, ∀ i < 36, repInS.contains i = false →
    wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) = 1 → liftsKB kb i = true →
    ∀ k < 64, (k = 0 ∨ ((mulM (k, 0, 0) (k, 0, 0)).1 = 0 ∧ (betaYM t i (k, 0, 0)).1 = k)) →
    (∃ x, (x ∈ allM ∧ fixKB kb t i x = true ∧ isInvKB kb x = true ∧
        eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x) = true) ∧ x.1 ≠ 0 ∧ x.1 ≠ k) ∨
      (∃ a b c d, (∀ x ∈ [a, b, c, d], x ∈ allM ∧ fixKB kb t i x = true ∧
          isInvKB kb x = true ∧ eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x) = true) ∧
        eqKB kb b a = false ∧ eqKB kb c a = false ∧ eqKB kb c b = false ∧
        eqKB kb d a = false ∧ eqKB kb d b = false ∧ eqKB kb d c = false) ∨
      (k ≠ 0 ∧ typeOf t i = expType kb ∧ (kbZero kb = true ∨ kbCyc kb = true) ∧
        (kbFull kb = true ∨ ∃ a b c, (∀ x ∈ [a, b, c], x ∈ allM ∧ fixKB kb t i x = true ∧
            isInvKB kb x = true ∧ eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x) = true) ∧
          eqKB kb b a = false ∧ eqKB kb c a = false ∧ eqKB kb c b = false)) := by
  refine fun kb hkb t ht i hi hS h2 hl k hk hkv => ?_
  rcases KernelL34W.d_spec kb hkb t ht i hi hS h2 hl k hk hkv with
    h | ⟨a, b, c, d, ha, hb, hc, hd, h⟩ | ⟨hk0, hty, hz, hf | ⟨a, b, c, ha, hb, hc, h⟩⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨a, b, c, d, fun x hx => ?_, h⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [ha, hb, hc, hd]
  · exact Or.inr (Or.inr ⟨hk0, hty, hz, Or.inl hf⟩)
  · refine Or.inr (Or.inr ⟨hk0, hty, hz, Or.inr ⟨a, b, c, fun x hx => ?_, h⟩⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    exacts [ha, hb, hc]

end Certificates
