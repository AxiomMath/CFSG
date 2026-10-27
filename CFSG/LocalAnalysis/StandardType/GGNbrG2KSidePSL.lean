module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2ASidesIso
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdModel

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggNbrG2K_psl_not_innDiag {F : Type} [Field F] [Finite F] (h3 : 3 ∣ Nat.card F - 1)
    {X : Type} [Group X] (θ : X ≃* Matrix.SpecialLinearGroup (Fin 3) F) (β : MulAut X)
    (d : Matrix.SpecialLinearGroup (Fin 3) F) {σ : F ≃+* F} (hσ : σ ≠ 1)
    (hβ : ∀ g : X, θ (β g) = d * Matrix.SpecialLinearGroup.map σ.toRingHom (θ g) * d⁻¹) :
    Nonempty (X ⧸ Subgroup.center X ≃* projectiveSL 3 F) ∧
      ¬ GGInnDiagPSL3 (Nat.card F) (X ⧸ Subgroup.center X) (centerQuotAut X β) := by
  let hcenter : (Subgroup.center X).map θ.toMonoidHom = scalars 3 F :=
    (Subgroup.map_center_eq θ).trans (scalars_eq_center 3 F).symm
  let e : X ⧸ Subgroup.center X ≃* projectiveSL 3 F :=
    QuotientGroup.congr (Subgroup.center X) (scalars 3 F) θ hcenter
  have he : ∀ x : X, e (x : X ⧸ Subgroup.center X) = proj 3 F (θ x) := by
    intro x
    change QuotientGroup.congr (Subgroup.center X) (scalars 3 F) θ hcenter
      (QuotientGroup.mk x) = proj 3 F (θ x)
    rw [QuotientGroup.congr_mk]
    rfl
  have hkey : MulAut.congr e (centerQuotAut X β) =
      conjAut 3 F (Matrix.SpecialLinearGroup.toGL d) * fieldAut 3 F σ := by
    ext y
    obtain ⟨q, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.trans_apply]
    conv_rhs => rw [he x]
    rw [centerQuotAut_mk, he, MulAut.mul_apply, fieldAut_proj, conjAut_proj, hβ x,
      TypeANbrDvd.slConjugation_toGL_eq]
  refine ⟨⟨e⟩, ?_⟩
  rw [ggInnDiagPSL3_iff h3 rfl e, hkey]
  intro hmem
  have hf : fieldAut 3 F σ ∈ linearAutGroup 3 F := by
    have hinv : (conjAut 3 F (Matrix.SpecialLinearGroup.toGL d))⁻¹ ∈ linearAutGroup 3 F :=
      inv_mem (conjAut_mem_linearAutGroup (n := 3) (K := F)
        (Matrix.SpecialLinearGroup.toGL d))
    simpa using mul_mem hinv hmem
  exact hσ ((CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_linearAutGroup_iff
    (n := 3) (K := F) (by norm_num)).mp hf)

end CFSG.StandardType

end
