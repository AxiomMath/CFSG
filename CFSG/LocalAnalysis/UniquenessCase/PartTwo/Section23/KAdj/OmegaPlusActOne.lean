module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusAct
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFamStab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped MatrixGroups

@[expose] noncomputable def plusRootEmbOne (K : Type) [Field K] : SL(2, K) →* PlusLin K :=
  (plusResExt K (show 1 + 2 = 3 from rfl)).comp (plusIotaOne K)

private lemma plusResExt_injective_E06 {K : Type} [Field K] :
    Function.Injective (plusResExt K (show 1 + 2 = 3 from rfl)) := by
  intro h₁ h₂ h
  apply autMat_injective
  have e1 := autMat_plusResExt (show 1 + 2 = 3 from rfl) h₁
  have e2 := autMat_plusResExt (show 1 + 2 = 3 from rfl) h₂
  rw [h] at e1
  have h3 := congrArg (fun M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K =>
      M.submatrix (plusResIdx (show 1 + 2 = 3 from rfl))
        (plusResIdx (show 1 + 2 = 3 from rfl))) (e1.symm.trans e2)
  simpa [submatrix_extendMat] using h3

private lemma plusIotaTwo_injective_E06 (K : Type) [Field K] :
    Function.Injective (plusIotaTwo K) := by
  intro A B h
  simp only [plusIotaTwo, MonoidHom.comp_apply] at h
  exact Matrix.SpecialLinearGroup.toGL_injective (levi_injective h)

private lemma plusIotaOne_injective_E06 (K : Type) [Field K] :
    Function.Injective (plusIotaOne K) := by
  intro A B h
  simp only [plusIotaOne, MonoidHom.comp_apply] at h
  exact plusIotaTwo_injective_E06 K ((MulAut.conj (swapPair K (1 : Fin 2))).injective h)

private lemma commute_torusElt_two_swapPair_E06 {K : Type} [Field K] (c : Kˣ) :
    Commute (torusElt 2 K ![c⁻¹, 1]) (swapPair K (1 : Fin 2)) := by
  rw [commute_iff_eq]
  apply LinearEquiv.ext
  intro v
  funext x
  simp only [LinearEquiv.mul_apply, torusElt_apply, swapPair_apply, Equiv.swap_apply_self]
  rcases x with i | i <;> fin_cases i <;>
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]

theorem plusRootEmbTwo_injective (K : Type) [Field K] : Function.Injective (plusRootEmbTwo K) := by
  intro A B h
  simp only [plusRootEmbTwo, MonoidHom.comp_apply] at h
  exact plusIotaTwo_injective_E06 K (plusResExt_injective_E06 h)

theorem plusRootEmbOne_injective (K : Type) [Field K] : Function.Injective (plusRootEmbOne K) := by
  intro A B h
  simp only [plusRootEmbOne, MonoidHom.comp_apply] at h
  exact plusIotaOne_injective_E06 K (plusResExt_injective_E06 h)

theorem torusElt_mul_plusRootEmbOne_mul_inv {K : Type} [Field K] {c b : Kˣ} (hb : b ^ 2 = c⁻¹)
    (A : SL(2, K)) :
    torusElt 3 K ![c, c⁻¹, 1] * plusRootEmbOne K A * (torusElt 3 K ![c, c⁻¹, 1])⁻¹ =
      plusRootEmbOne K (plusDiagSL2 b * A * (plusDiagSL2 b)⁻¹) := by
  have hconj : MulAut.conj (torusElt 2 K ![c⁻¹, 1]) (swapPair K (1 : Fin 2)) =
      swapPair K (1 : Fin 2) := by
    rw [MulAut.conj_apply, (commute_torusElt_two_swapPair_E06 c).eq, mul_assoc,
      mul_inv_cancel, mul_one]
  have hmain : torusElt 2 K ![c⁻¹, 1] *
        (swapPair K (1 : Fin 2) * plusIotaTwo K A * swapPair K (1 : Fin 2)) *
        (torusElt 2 K ![c⁻¹, 1])⁻¹ =
      swapPair K (1 : Fin 2) *
        plusIotaTwo K (plusDiagSL2 b * A * (plusDiagSL2 b)⁻¹) *
        swapPair K (1 : Fin 2) := by
    calc
      torusElt 2 K ![c⁻¹, 1] *
          (swapPair K (1 : Fin 2) * plusIotaTwo K A * swapPair K (1 : Fin 2)) *
          (torusElt 2 K ![c⁻¹, 1])⁻¹
          = MulAut.conj (torusElt 2 K ![c⁻¹, 1])
              (swapPair K (1 : Fin 2) * plusIotaTwo K A * swapPair K (1 : Fin 2)) := by
            rw [MulAut.conj_apply]
      _ = MulAut.conj (torusElt 2 K ![c⁻¹, 1]) (swapPair K (1 : Fin 2)) *
            MulAut.conj (torusElt 2 K ![c⁻¹, 1]) (plusIotaTwo K A) *
            MulAut.conj (torusElt 2 K ![c⁻¹, 1]) (swapPair K (1 : Fin 2)) := by
            rw [map_mul, map_mul]
      _ = swapPair K (1 : Fin 2) *
            (torusElt 2 K ![c⁻¹, 1] * plusIotaTwo K A * (torusElt 2 K ![c⁻¹, 1])⁻¹) *
            swapPair K (1 : Fin 2) := by
            rw [hconj, MulAut.conj_apply]
      _ = swapPair K (1 : Fin 2) *
            plusIotaTwo K (plusDiagSL2 b * A * (plusDiagSL2 b)⁻¹) *
            swapPair K (1 : Fin 2) := by
            rw [torusElt_two_mul_plusIotaTwo_mul_inv hb A]
  simp only [plusRootEmbOne, MonoidHom.comp_apply, plusIotaOne_apply]
  rw [torusElt_mul_plusResExt_mul_inv]
  exact congrArg (fun g => plusResExt K (show 1 + 2 = 3 from rfl) g) hmain

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
