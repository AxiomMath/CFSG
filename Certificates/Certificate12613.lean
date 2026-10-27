
module

public import Certificates.Certificate12613Base

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24Check
public import CFSG.Monster.B.Mathieu.M24CheckInputs
import Certificates.Kernel.M24Three.Glue
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24Base
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

open CFSG.KD.M24Three

namespace Certificates

open CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24 CFSG.Sporadic.Th CFSG.Blueprint Subgroup in
theorem certificate12613 :
    (∀ t ∈ NativeSporadic.M24, orderOf t = 3 → ∃ g ∈ NativeSporadic.M24,
      t = g * wordG letG xW * g⁻¹ ∨ t = g * wordG letG x2W * g⁻¹) ∧
    (closure {wordG letG s1W, wordG letG s2W} ≤ NativeSporadic.M24 ∧
      Nat.card ↥(closure {wordG letG s1W, wordG letG s2W}) = 27) ∧
    (closure {wordG letG ca1W, wordG letG ca2W} =
        NativeSporadic.M24 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 24))) ∧
      Nat.card ↥(NativeSporadic.M24 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 24)))) =
        1080 ∧
      (∀ y ∈ NativeSporadic.M24 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 24))),
        (orderOf y).Prime → orderOf y ≠ 3 → ∃ r ∈ [ra0W, ra1W, ra2W],
          ∃ c ∈ NativeSporadic.M24 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 24))),
            y = c * wordG letG r * c⁻¹) ∧
      ∀ p ∈ [(ra0W, ha0W), (ra1W, ha1W), (ra2W, ha2W)],
        wordG letG p.2 ∈
          NativeSporadic.M24 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 24))) ∧
        3 ∣ orderOf (wordG letG p.1 * (wordG letG p.2 * wordG letG p.1 * (wordG letG p.2)⁻¹))) ∧
    (Nat.card ↥(NativeSporadic.M24 ⊓ centralizer ({wordG letG x2W} : Set (Equiv.Perm (Fin 24)))) =
        504 ∧
      (∀ y ∈ NativeSporadic.M24 ⊓ centralizer ({wordG letG x2W} : Set (Equiv.Perm (Fin 24))),
        (orderOf y).Prime → orderOf y ≠ 3 → ∃ r ∈ [rb0W, rb1W, rb2W],
          ∃ c ∈ NativeSporadic.M24 ⊓ centralizer ({wordG letG x2W} : Set (Equiv.Perm (Fin 24))),
            y = c * wordG letG r * c⁻¹) ∧
      ∀ p ∈ [(rb0W, hb0W), (rb1W, hb1W), (rb2W, hb2W)],
        wordG letG p.2 ∈
          NativeSporadic.M24 ⊓ centralizer ({wordG letG x2W} : Set (Equiv.Perm (Fin 24))) ∧
        3 ∣ orderOf (wordG letG p.1 * (wordG letG p.2 * wordG letG p.1 * (wordG letG p.2)⁻¹))) :=
  ⟨m24_conj3, ⟨Subgroup.closure_le _ |>.2 (by
      rintro g (rfl | rfl)
      · exact CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.wordG_mem _
      · exact CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.wordG_mem _), m24_sylow27⟩,
    ⟨m24_cent3A_eq, m24_card3A, m24_cover3A, m24_wit3A⟩, ⟨m24_card3B, m24_cover3B, m24_wit3B⟩⟩

end Certificates
