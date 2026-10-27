module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcSimpleSystemConjugacy
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcRootReflectionRelations

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

@[expose] def rootFamilyMap (γ : Fin τ.rank → Fin τ.rank → ℤ) : Module.End ℤ (Fin τ.rank → ℤ) :=
  Fintype.linearCombination ℤ γ

theorem rootFamilyMap_apply (γ : Fin τ.rank → Fin τ.rank → ℤ) (x : Fin τ.rank → ℤ) :
    rootFamilyMap γ x = ∑ i, x i • γ i :=
  Fintype.linearCombination_apply ℤ γ x

theorem rootFamilyMap_single (γ : Fin τ.rank → Fin τ.rank → ℤ) (i : Fin τ.rank) :
    rootFamilyMap γ (Pi.single i 1) = γ i := by
  simp [rootFamilyMap]

theorem iform_rootFamilyMap_apply (γ : Fin τ.rank → Fin τ.rank → ℤ)
    (x y : Fin τ.rank → ℤ) :
    iform (rootFamilyMap γ x) (rootFamilyMap γ y) = ∑ i, ∑ j, x i * y j * iform (γ i) (γ j) := by
  rw [rootFamilyMap_apply, rootFamilyMap_apply, iform_finset_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iform_finset_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iform_smul_left, iform_smul_right]
  ring

theorem iform_rootFamilyMap (hτ : ∀ i, τ.symmetrizer i i = 1)
    {γ : Fin τ.rank → Fin τ.rank → ℤ} (hγ : ∀ i j, iform (γ i) (γ j) = τ.cartan i j)
    (x y : Fin τ.rank → ℤ) :
    iform (rootFamilyMap γ x) (rootFamilyMap γ y) = iform x y := by
  have hsingle : ∀ i j : Fin τ.rank,
      iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single j 1) = τ.cartan i j := by
    intro i j
    rw [iform_single_left, Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp),
      Pi.single_eq_same, mul_one, hτ i, one_mul]
  have hident : ∀ z : Fin τ.rank → ℤ,
      rootFamilyMap (fun i => (Pi.single i 1 : Fin τ.rank → ℤ)) z = z := by
    intro z
    rw [rootFamilyMap_apply]
    exact (pi_eq_sum_univ' z).symm
  calc iform (rootFamilyMap γ x) (rootFamilyMap γ y)
      = ∑ i, ∑ j, x i * y j * iform (γ i) (γ j) := iform_rootFamilyMap_apply γ x y
    _ = ∑ i, ∑ j, x i * y j * τ.cartan i j := by simp [hγ]
    _ = ∑ i, ∑ j, x i * y j *
          iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single j 1) := by simp [hsingle]
    _ = iform (rootFamilyMap (fun i => (Pi.single i 1 : Fin τ.rank → ℤ)) x)
          (rootFamilyMap (fun i => (Pi.single i 1 : Fin τ.rank → ℤ)) y) :=
        (iform_rootFamilyMap_apply (fun i => (Pi.single i 1 : Fin τ.rank → ℤ)) x y).symm
    _ = iform x y := by rw [hident x, hident y]

theorem rootFamilyMap_smul_simple (hτ : ∀ i, τ.symmetrizer i i = 1)
    {γ : Fin τ.rank → Fin τ.rank → ℤ} (hγ : ∀ i j, iform (γ i) (γ j) = τ.cartan i j)
    (hroot : ∀ i, IsRoot τ (γ i)) (i : Fin τ.rank) (x : Fin τ.rank → ℤ) :
    rootFamilyMap γ (simple τ i • x) = rootReflection (γ i) • rootFamilyMap γ x := by
  have hii : iform (γ i) (γ i) = 2 :=
    CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two hτ (hroot i)
  have hc : corootPair (γ i) (rootFamilyMap γ x) = ∑ j, τ.cartan i j * x j := by
    have h2 : iform (γ i) (rootFamilyMap γ x) = ∑ j, τ.cartan i j * x j := by
      rw [← rootFamilyMap_single γ i, iform_rootFamilyMap hτ hγ, iform_single_left, hτ i,
        one_mul]
    refine mul_right_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num) ?_
    conv_lhs => rw [← hii, corootPair_mul (hroot i), h2]
    ring
  rw [simple_smul, reflect, map_sub, map_smul, rootFamilyMap_single,
    rootReflection_smul (hroot i), hc]

theorem rootFamilyMap_smul (hτ : ∀ i, τ.symmetrizer i i = 1)
    {γ : Fin τ.rank → Fin τ.rank → ℤ} (hγ : ∀ i j, iform (γ i) (γ j) = τ.cartan i j)
    (hroot : ∀ i, IsRoot τ (γ i)) (α : WeylGroup τ →* WeylGroup τ)
    (hα : ∀ i, α (simple τ i) = rootReflection (γ i)) (w : WeylGroup τ)
    (x : Fin τ.rank → ℤ) : rootFamilyMap γ (w • x) = α w • rootFamilyMap γ x := by
  induction w using (coxeterSystem τ).simple_induction_left with
  | one => simp
  | mul_simple_left w i ih =>
    rw [mul_smul, rootFamilyMap_smul_simple hτ hγ hroot i, ih, map_mul, hα, mul_smul]

theorem isRoot_rootFamilyMap (hτ : ∀ i, τ.symmetrizer i i = 1)
    {γ : Fin τ.rank → Fin τ.rank → ℤ} (hγ : ∀ i j, iform (γ i) (γ j) = τ.cartan i j)
    (hroot : ∀ i, IsRoot τ (γ i)) (α : WeylGroup τ →* WeylGroup τ)
    (hα : ∀ i, α (simple τ i) = rootReflection (γ i)) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    IsRoot τ (rootFamilyMap γ β) := by
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  rw [rootFamilyMap_smul hτ hγ hroot α hα w, rootFamilyMap_single]
  exact IsRoot.smul (hroot j) (α w)

theorem exists_weyl_smul_rootFamily_eq_single (hτ : ∀ i, τ.symmetrizer i i = 1)
    {γ : Fin τ.rank → Fin τ.rank → ℤ} (hγ : ∀ i j, iform (γ i) (γ j) = τ.cartan i j)
    (hroot : ∀ i, IsRoot τ (γ i)) (α : WeylGroup τ →* WeylGroup τ)
    (hα : ∀ i, α (simple τ i) = rootReflection (γ i)) :
    ∃ u : WeylGroup τ, ∀ i, ∃ j, u • γ i = Pi.single j 1 := by
  obtain ⟨u, hu⟩ := exists_weyl_smul_isometry_single_eq_single hτ
    (iform_rootFamilyMap hτ hγ) (fun β hβ => isRoot_rootFamilyMap hτ hγ hroot α hα hβ)
  refine ⟨u, fun i => ?_⟩
  obtain ⟨j, hj⟩ := hu i
  exact ⟨j, by rwa [rootFamilyMap_single] at hj⟩

end CFSG.StandardType

end
