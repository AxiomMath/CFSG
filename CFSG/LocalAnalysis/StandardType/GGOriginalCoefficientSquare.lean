module
public import CFSG.LocalAnalysis.StandardType.GGActualQuadraticField
public noncomputable section
namespace CFSG.StandardType.GGFinModel

theorem exists_original_coefficient_square
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    (ι : K ≃+* actualQuadraticSubfield n) :
    ∃ η : GaloisField 2 (2 * n) ≃+* K,
      ((actualQuadraticSubfield n).subtype.comp ι.toRingHom).comp η.toRingHom =
        ggRatEmb (2 * n) := by
  let j : GaloisField 2 (2 * n) →+* actualQuadraticSubfield n :=
    (ggRatEmb (2 * n)).codRestrict (actualQuadraticSubfield n) (fun x => by
      change ggRatEmb (2 * n) x ∈ (actualQuadraticSubfield n : Set GGL)
      rw [coe_actualQuadraticSubfield_eq_range hn]
      exact ⟨x, rfl⟩)
  have hj : Function.Bijective j := by
    refine ⟨j.injective, ?_⟩
    intro y
    have hy : (y : GGL) ∈ Set.range (ggRatEmb (2 * n)) := by
      rw [← coe_actualQuadraticSubfield_eq_range hn]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let η := (RingEquiv.ofBijective j hj).trans ι.symm
  refine ⟨η, ?_⟩
  apply RingHom.ext
  intro x
  change (ι (ι.symm (j x)) : GGL) = ggRatEmb (2 * n) x
  rw [ι.apply_symm_apply]
  rfl

end CFSG.StandardType.GGFinModel
