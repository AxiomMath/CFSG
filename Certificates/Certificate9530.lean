module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Data
import Certificates.Kernel.Sz32.Assembly
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Cone

public section

namespace Certificates

open CFSG.AGLEmbedding.KFactProofs.Sz32 CFSG.KC.Sz32T Matrix

open CFSG.AGLEmbedding.KFactProofs.Sz32 Matrix in
theorem certificate9530 : ∀ M : Matrix (Fin 4) (Fin 4) F32, Commute M (g0Mat ^ 5) → M.det = 1 →
    (∀ u v : F32, OnOmegaGen 2 (M *ᵥ lineVec u v)) → OnOmegaGen 2 (M *ᵥ inftyVec) →
    ∃ k < 25, M = g0Mat ^ k := by
  intro M hcomm hdet hline hinfty
  rw [← t0Mat_eq] at hcomm
  have hpoly := eq_polyMat_of_commute hcomm
  have key : ∀ {l : F32} {w : Vec}, l ≠ 0 → (w = inftyVec ∨ ∃ u v : F32, w = lineVec u v) →
      M *ᵥ e0 = l • w → ∃ k < 25, M = g0Mat ^ k := by
    intro l w hl hw he
    have hM : M = l • Pw w := by
      refine hpoly.trans ?_
      rw [he, Matrix.mulVec_smul]
      exact polyMat_smul _ _ _ _ _
    have htest : ∀ p : Vec, OnOmegaGen 2 (M *ᵥ p) → OnOmegaGen 2 (Pw w *ᵥ p) := by
      intro p hp
      rw [hM, Matrix.smul_mulVec] at hp
      exact (onOmegaGen_smul hl _).1 hp
    obtain ⟨k, hk, l', hl'⟩ := ovoid_check hw (htest _ (hline 1 0)) (htest _ (hline omega 0))
    rw [hl', smul_smul] at hM
    have h1 := hdet
    rw [hM, Matrix.det_smul, Matrix.det_pow, det_g0Mat, one_pow, mul_one, Fintype.card_fin] at h1
    exact ⟨k, hk, by rw [hM, pow_four_eq_one _ h1, one_smul]⟩
  have hw : OnOmegaGen 2 (M *ᵥ e0) := by
    rw [e0_eq_lineVec]
    exact hline 0 0
  rcases exists_cone hw with ⟨l, hl, u, v, he⟩ | ⟨l, hl, he⟩
  · exact key hl (Or.inr ⟨u, v, rfl⟩) he
  · exact key hl (Or.inl rfl) he

end Certificates
