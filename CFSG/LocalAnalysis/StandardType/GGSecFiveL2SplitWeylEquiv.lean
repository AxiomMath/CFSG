module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

private theorem exists_groupEquiv_of_eq {B : Type} {M N : CoxeterMatrix B} (h : M = N) :
    ∃ φ : M.Group ≃* N.Group, ∀ i, φ (M.simple i) = N.simple i := by
  subst h
  exact ⟨MulEquiv.refl _, fun _ => rfl⟩

theorem ggDk_weylEquiv {ι : Type} {M : CoxeterMatrix ι} {k : ℕ} {σ : Fin k ≃ ι}
    (hM : M = (ggCoxeterMatrixD k).reindex σ) : ∃ φ : M.Group ≃* ggWeylD k,
      ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a := by
  have hC : GGIntCartan (ggCoxeterMatrixD k) (cartanD k) := by
    rw [cartanD_eq k]
    exact ggIntCartan_D k
  obtain ⟨ψ, hψ⟩ :=
    exists_groupEquiv_of_eq (coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartanD k) hC).symm
  subst hM
  refine ⟨((ggCoxeterMatrixD k).reindexGroupEquiv σ).trans ψ, fun a => ?_⟩
  rw [MulEquiv.trans_apply, CoxeterMatrix.reindexGroupEquiv_apply_simple,
    Equiv.symm_apply_apply, hψ]

end CFSG.StandardType

end
