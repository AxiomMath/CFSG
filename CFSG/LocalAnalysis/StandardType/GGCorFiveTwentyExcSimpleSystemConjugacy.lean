module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcIsometryRoots
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcPositiveRootDecomposition

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootSpace

variable {τ : Tag}

theorem inner_ofLattice_realExtend_heightVector {θ : Module.End ℤ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y) (v : Fin τ.rank → ℤ) :
    inner ℝ (ofLattice (θ v)) (realExtend θ (heightVector τ)) = (height v : ℝ) := by
  rw [← realExtend_ofLattice θ v, inner_realExtend_realExtend hθ]
  exact inner_ofLattice_heightVector v

theorem inner_ofLattice_smul_weylAct_realExtend_heightVector
    {θ : Module.End ℤ (Fin τ.rank → ℤ)} (hθ : ∀ x y, iform (θ x) (θ y) = iform x y)
    (u : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    inner ℝ (ofLattice (u • θ v)) (weylAct τ u (realExtend θ (heightVector τ))) =
      (height v : ℝ) := by
  rw [← weylAct_ofLattice u (θ v), LinearIsometryEquiv.inner_map_map]
  exact inner_ofLattice_realExtend_heightVector hθ v

theorem exists_weylAct_realExtend_heightVector_mem_openDominantCone
    {θ : Module.End ℤ (Fin τ.rank → ℤ)} (hθ : ∀ x y, iform (θ x) (θ y) = iform x y)
    (hΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α)) :
    ∃ u : WeylGroup τ, weylAct τ u (realExtend θ (heightVector τ)) ∈ openDominantCone τ := by
  have hreg : ∀ α, IsRoot τ α →
      inner ℝ (ofLattice α) (realExtend θ (heightVector τ)) ≠ 0 := by
    intro α hα
    obtain ⟨γ, hγ, hγeq⟩ := exists_isRoot_eq_of_iform_isometry hθ hΦ hα
    rw [← hγeq, inner_ofLattice_realExtend_heightVector hθ γ]
    exact Int.cast_ne_zero.mpr (IsRoot.height_ne_zero hγ)
  obtain ⟨w, y, hy, hwy⟩ := exists_weylAct_mem_dominantCone (realExtend θ (heightVector τ))
  refine ⟨w⁻¹, fun i => ?_⟩
  have hyw : weylAct τ w⁻¹ (realExtend θ (heightVector τ)) = y := by
    rw [hwy, ← weylAct_mul_apply, inv_mul_cancel, map_one]
    simp
  rw [hyw]
  have hne : inner ℝ (ofLattice (Pi.single i 1)) y ≠ 0 := by
    rw [← hyw]
    have hcomp : weylAct τ w⁻¹ (weylAct τ (w⁻¹)⁻¹ (ofLattice (Pi.single i 1))) =
        ofLattice (Pi.single i 1) := by
      rw [← weylAct_mul_apply, mul_inv_cancel, map_one]
      simp
    calc inner ℝ (ofLattice (Pi.single i 1))
          (weylAct τ w⁻¹ (realExtend θ (heightVector τ)))
        = inner ℝ (weylAct τ w⁻¹ (weylAct τ (w⁻¹)⁻¹ (ofLattice (Pi.single i 1))))
            (weylAct τ w⁻¹ (realExtend θ (heightVector τ))) := by rw [hcomp]
      _ = inner ℝ (weylAct τ (w⁻¹)⁻¹ (ofLattice (Pi.single i 1)))
            (realExtend θ (heightVector τ)) :=
          LinearIsometryEquiv.inner_map_map (weylAct τ w⁻¹) _ _
      _ ≠ 0 := by
          rw [weylAct_ofLattice]
          exact hreg _ (IsRoot.smul (isRoot_single τ i) (w⁻¹)⁻¹)
  exact lt_of_le_of_ne (hy i) (Ne.symm hne)

theorem height_pos_smul_isometry_single {θ : Module.End ℤ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y) (hΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α))
    {u : WeylGroup τ}
    (hu : weylAct τ u (realExtend θ (heightVector τ)) ∈ openDominantCone τ) (i : Fin τ.rank) :
    0 < height (u • θ (Pi.single i 1 : Fin τ.rank → ℤ)) := by
  have hroot : IsRoot τ (u • θ (Pi.single i 1 : Fin τ.rank → ℤ)) :=
    IsRoot.smul (hΦ (Pi.single i 1) (isRoot_single τ i)) u
  by_contra h
  have hneg : height (u • θ (Pi.single i 1 : Fin τ.rank → ℤ)) < 0 :=
    lt_of_le_of_ne (not_lt.1 h) hroot.height_ne_zero
  have hpos' : 0 < height (-(u • θ (Pi.single i 1 : Fin τ.rank → ℤ))) := by
    rw [height_neg]; omega
  have hcontr := IsRoot.inner_pos_of_mem_openDominantCone (IsRoot.neg hroot) hpos' hu
  rw [ofLattice_neg, inner_neg_left,
    inner_ofLattice_smul_weylAct_realExtend_heightVector hθ u (Pi.single i 1),
    height_single] at hcontr
  norm_num at hcontr

theorem smul_isometry_single_ne_add {θ : Module.End ℤ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y) (hΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α))
    {u : WeylGroup τ}
    (hu : weylAct τ u (realExtend θ (heightVector τ)) ∈ openDominantCone τ) (i : Fin τ.rank)
    {a b : Fin τ.rank → ℤ} (ha : IsRoot τ a) (hb : IsRoot τ b) (hapos : 0 < height a)
    (hbpos : 0 < height b) : u • θ (Pi.single i 1 : Fin τ.rank → ℤ) ≠ a + b := by
  intro h
  obtain ⟨a', ha', ha'eq⟩ :=
    exists_isRoot_eq_of_iform_isometry hθ hΦ (IsRoot.smul ha u⁻¹)
  obtain ⟨b', hb', hb'eq⟩ :=
    exists_isRoot_eq_of_iform_isometry hθ hΦ (IsRoot.smul hb u⁻¹)
  have hua : u • θ a' = a := by rw [ha'eq, smul_inv_smul]
  have hub : u • θ b' = b := by rw [hb'eq, smul_inv_smul]
  have hθab : θ (a' + b') = θ (Pi.single i 1 : Fin τ.rank → ℤ) := by
    rw [map_add, ha'eq, hb'eq, ← smul_add, ← h, inv_smul_smul]
  have hab : a' + b' = Pi.single i 1 := injective_of_iform_isometry hθ hθab
  have hha : (height a' : ℝ) =
      inner ℝ (ofLattice a) (weylAct τ u (realExtend θ (heightVector τ))) := by
    rw [← inner_ofLattice_smul_weylAct_realExtend_heightVector hθ u a', hua]
  have hhb : (height b' : ℝ) =
      inner ℝ (ofLattice b) (weylAct τ u (realExtend θ (heightVector τ))) := by
    rw [← inner_ofLattice_smul_weylAct_realExtend_heightVector hθ u b', hub]
  have ha'ge : 1 ≤ height a' := by
    have hpos : 0 < (height a' : ℝ) := by
      rw [hha]
      exact IsRoot.inner_pos_of_mem_openDominantCone ha hapos hu
    have hInt : 0 < height a' := by exact_mod_cast hpos
    omega
  have hb'ge : 1 ≤ height b' := by
    have hpos : 0 < (height b' : ℝ) := by
      rw [hhb]
      exact IsRoot.inner_pos_of_mem_openDominantCone hb hbpos hu
    have hInt : 0 < height b' := by exact_mod_cast hpos
    omega
  have hh : height a' + height b' = 1 := by
    have h' := congrArg height hab
    rwa [height_add, height_single] at h'
  omega

theorem exists_weyl_smul_isometry_single_eq_single (hτ : ∀ i, τ.symmetrizer i i = 1)
    {θ : Module.End ℤ (Fin τ.rank → ℤ)} (hθ : ∀ x y, iform (θ x) (θ y) = iform x y)
    (hΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α)) :
    ∃ u : WeylGroup τ, ∀ i, ∃ j, u • θ (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single j 1 := by
  obtain ⟨u, hu⟩ := exists_weylAct_realExtend_heightVector_mem_openDominantCone hθ hΦ
  refine ⟨u, fun i => ?_⟩
  have hroot : IsRoot τ (u • θ (Pi.single i 1 : Fin τ.rank → ℤ)) :=
    IsRoot.smul (hΦ (Pi.single i 1) (isRoot_single τ i)) u
  have hpos := height_pos_smul_isometry_single hθ hΦ hu i
  rcases isRoot_eq_single_or_exists_add hτ hroot hpos with ⟨j, hj⟩ |
    ⟨a, b, ha, hb, hapos, hbpos, hab⟩
  · exact ⟨j, hj⟩
  · exact absurd hab (smul_isometry_single_ne_add hθ hΦ hu i ha hb hapos hbpos)

end CFSG.StandardType

end
