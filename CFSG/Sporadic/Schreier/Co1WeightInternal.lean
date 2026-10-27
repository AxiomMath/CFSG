module

public import CFSG.Sporadic.Schreier.Co1WeightProj

public section

namespace CFSG.Sporadic.Co1Schreier.WeightProj

open Matrix

variable {K : Type*} [Field K] [CharP K 2] {w : K} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) {n : ℕ}
  {R : (Fin 6 → ZMod 3) → Matrix (Fin n) (Fin n) K} (hR : ∀ b b', R (b + b') = R b * R b')
  (hR0 : R 0 = 1)

include hw3 hw1 hR hR0 in
theorem isInternal_wtSpace : DirectSum.IsInternal fun f => wtSpace (w := w) R f := by
  have h : DirectSum.coeLinearMap (fun f => wtSpace (w := w) R f) =
      (wtEquiv hw3 hw1 hR hR0).symm.toLinearMap ∘ₗ
        (DirectSum.linearEquivFunOnFintype K _ fun f => wtSpace (w := w) R f).toLinearMap := by
    refine DirectSum.linearMap_ext K fun f => LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, DirectSum.coeLinearMap_lof,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      DirectSum.linearEquivFunOnFintype_lof]
    change (x : Fin n → K) = ∑ g, ((Pi.single f x : ∀ g, wtSpace (w := w) R g) g : Fin n → K)
    rw [Finset.sum_eq_single f (fun g _ hg => by rw [Pi.single_eq_of_ne hg, Submodule.coe_zero])
      (fun h => absurd (Finset.mem_univ f) h), Pi.single_eq_same]
  change Function.Bijective (DirectSum.coeLinearMap fun f => wtSpace (w := w) R f)
  rw [h, LinearMap.coe_comp]
  exact (wtEquiv hw3 hw1 hR hR0).symm.bijective.comp
    (DirectSum.linearEquivFunOnFintype K _ fun f => wtSpace (w := w) R f).bijective

include hw3 hw1 hR hR0 in
theorem isInternal_wtSpace_comp {ι : Type*} [DecidableEq ι] {φ : ι → Fin 6 → ZMod 3}
    (hφ : Function.Injective φ) (hbot : ∀ f, (∀ i, φ i ≠ f) → wtSpace (w := w) R f = ⊥) :
    DirectSum.IsInternal fun i => wtSpace (w := w) R (φ i) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    ((isInternal_wtSpace hw3 hw1 hR hR0).submodule_iSupIndep.comp hφ) ?_
  rw [eq_top_iff]
  intro v _
  rw [← sum_wtProj hw3 hw1 hR0 v]
  refine Submodule.sum_mem _ fun f _ => ?_
  by_cases hf : ∃ i, φ i = f
  · obtain ⟨i, rfl⟩ := hf
    exact Submodule.mem_iSup_of_mem i (wtProj_mulVec_mem hw3 hR _ v)
  · have h0 := wtProj_mulVec_mem hw3 hR f v
    rw [hbot f fun i hi => hf ⟨i, hi⟩, Submodule.mem_bot] at h0
    rw [h0]
    exact zero_mem _

end CFSG.Sporadic.Co1Schreier.WeightProj
