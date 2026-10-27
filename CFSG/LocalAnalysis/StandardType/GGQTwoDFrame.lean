module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCells

public section

namespace CFSG.StandardType.QTwo

section Frame

variable {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
  {ι : Type} {m : ℕ} {e' : Fin m ≃ ι}

theorem orbAt_of_frame_of_conj {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hF : QTwoFrameAt Bs X M A e e')
    {T : Finset (Fin m)} (hT : ∃ w : (ggCoxeterMatrixD m).Group, ∀ t ∈ T,
      w * (ggCoxeterMatrixD m).simple t * w⁻¹ ∈ qtwoParabRefl m) :
    GGOrbAt X Bs e e' T := by
  subst hM
  obtain ⟨w₀, hw₀⟩ := hF
  obtain ⟨w, hw⟩ := hT
  let ε := ((ggCoxeterMatrixD m).reindexGroupEquiv e').symm
  have hε : ∀ i, ε ((ggCoxeterMatrixD m).simple i) =
      ((ggCoxeterMatrixD m).reindex e').simple (e' i) := fun i => rfl
  let φ : (ggCoxeterMatrixD m).Group →* MulAut ↥Bs :=
    (A.subtype.comp e.toMonoidHom).comp ((MulAut.conj w₀).toMonoidHom.comp ε.toMonoidHom)
  have hφ : ∀ u, φ u = ((e (w₀ * ε u * w₀⁻¹) : ↥A) : MulAut ↥Bs) := fun u => rfl
  have hS : ∀ u ∈ Subgroup.closure
      ((ggCoxeterMatrixD m).simple '' {j : Fin m | (j : ℕ) ≠ 0}), φ u ∈ ggAutomizer X Bs := by
    intro u hu
    have hle : Subgroup.closure ((ggCoxeterMatrixD m).simple '' {j : Fin m | (j : ℕ) ≠ 0}) ≤
        (ggAutomizer X Bs).comap φ := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      show φ ((ggCoxeterMatrixD m).simple j) ∈ ggAutomizer X Bs
      rw [hφ, hε]
      exact hw₀ j hj
    exact hle hu
  refine ⟨w₀ * ε w, fun t ht => ?_⟩
  obtain ⟨i, hi0, u, hu, hEq⟩ := hw t ht
  have e1 : (w₀ * ε w) * ((ggCoxeterMatrixD m).reindex e').simple (e' t) * (w₀ * ε w)⁻¹ =
      w₀ * ε (w * (ggCoxeterMatrixD m).simple t * w⁻¹) * w₀⁻¹ := by
    rw [← hε t, map_mul, map_mul, map_inv]
    group
  rw [e1, hEq]
  have e2 : ((e (w₀ * ε (u * (ggCoxeterMatrixD m).simple i * u⁻¹) * w₀⁻¹) : ↥A) :
      MulAut ↥Bs) = φ (u * (ggCoxeterMatrixD m).simple i * u⁻¹) := rfl
  rw [e2, map_mul, map_mul, map_inv]
  exact mul_mem (mul_mem (hS u hu)
    (hS _ (Subgroup.subset_closure ⟨i, hi0, rfl⟩))) (inv_mem (hS u hu))

theorem orbAt_of_frame {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (hP : QTwoParabConj)
    (hm : 7 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hF : QTwoFrameAt Bs X M A e e') {T : Finset (Fin m)} (hT : QTwoPattern m T) :
    GGOrbAt X Bs e e' T :=
  orbAt_of_frame_of_conj e hM hF (hP m hm T hT)

end Frame

end CFSG.StandardType.QTwo

end
