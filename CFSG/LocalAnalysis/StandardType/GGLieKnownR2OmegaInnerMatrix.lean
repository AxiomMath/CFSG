module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerFieldFrame
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerSimilarity
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerMatrixFrame
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalSetting
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalSettingW

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.LieKnownR2.POmega.Radical
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem
open CFSG.ClassicalGroups.Orthogonal
open Matrix TauCeti
open CFSG.ComponentClassification.CatalogueBHigherLinearField

namespace CFSG.StandardType.LieKnownR2.POmega.Inner

theorem ggRootNormInner_semilinear_plus {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {β : Fin (Spin.plusDatum n F (by omega)).rank → ℤ}
    (hβ : β ∈ (Spin.plusDatum n F (by omega)).roots) (u : ↥(spinGroup (Spin.quadPlus n F))) :
    ∀ (A : GL (Fin n ⊕ Fin n) F) (φ : F ≃+* F) (μ : Fˣ),
      GGSemilinearSimilitude (Spin.quadPlus n F) A φ μ →
      ∀ y : MulAut ↥(spinGroup (Spin.quadPlus n F)),
        (∃ k : ℕ, y ^ 2 ^ k = 1) →
        GGTrivialOnNormalizer
          (((Spin.plusDatum n F (by omega)).rootGroup β).map (MulAut.conj u).toMonoidHom) y →
        GGMatrixSemilinearAction (Spin.quadPlus n F) A φ μ y →
        ∃ k : ↥(spinGroup (Spin.quadPlus n F)), y = MulAut.conj k := by
  intro A φ μ hsim y hy2 htriv hmat
  have hS : SpinOmegaData (Spin.quadPlus n F) := spinOmegaData_quadPlus (by omega)
  obtain ⟨P, P', horth, hR, hW⟩ := exists_frame_hW_of_root_plus hn hS hβ u
  have htriv' : GGTrivialOnNormalizer (siegelRoot (Spin.quadPlus n F) P.e P'.e) y := by
    rw [← hR]; exact htriv
  have hV : 6 ≤ Module.finrank F (Fin n ⊕ Fin n → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  exact ggRootNormInner_semilinear_frame hS horth hV hW hsim y hy2 htriv' hmat

theorem ggRootNormInner_semilinear_minus {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {β : Fin (Spin.Twisted.minusDatum n hirr).rank → ℤ}
    (hβ : β ∈ (Spin.Twisted.minusDatum n hirr).roots)
    (hl : GGLongRoot (Spin.Twisted.minusDatum n hirr) β)
    (u : ↥(spinGroup (Spin.quadMinus n F b c))) :
    ∀ (A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) (φ : F ≃+* F) (μ : Fˣ),
      GGSemilinearSimilitude (Spin.quadMinus n F b c) A φ μ →
      ∀ y : MulAut ↥(spinGroup (Spin.quadMinus n F b c)),
        (∃ k : ℕ, y ^ 2 ^ k = 1) →
        GGTrivialOnNormalizer
          (((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom) y →
        GGMatrixSemilinearAction (Spin.quadMinus n F b c) A φ μ y →
        ∃ k : ↥(spinGroup (Spin.quadMinus n F b c)), y = MulAut.conj k := by
  intro A φ μ hsim y hy2 htriv hmat
  have hS : SpinOmegaData (Spin.quadMinus n F b c) := spinOmegaData_quadMinus hn hirr
  obtain ⟨P, P', horth, hR, hW⟩ := exists_frame_hW_of_root_minus hn hirr hS hβ hl u
  have htriv' : GGTrivialOnNormalizer (siegelRoot (Spin.quadMinus n F b c) P.e P'.e) y := by
    rw [← hR]; exact htriv
  have hV : 6 ≤ Module.finrank F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin]
    omega
  exact ggRootNormInner_semilinear_frame hS horth hV hW hsim y hy2 htriv' hmat

end CFSG.StandardType.LieKnownR2.POmega.Inner
