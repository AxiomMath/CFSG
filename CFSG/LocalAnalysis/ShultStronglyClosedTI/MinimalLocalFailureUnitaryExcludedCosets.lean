module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismCoset

public section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open scoped Pointwise

namespace Cosets

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {J : HermitianForm 3 K} {q : ℕ} {V : Subgroup G} {φ : hermitianUnipotentCoord J ≃* V} {u : G}

theorem isConj_mul_of_mem_normalizer (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) (ht : u ^ 2 = 1)
    (huV : ∀ v : V, u * (v : G) * u⁻¹ = (fieldInvolution J φ v : G))
    (hΔ : ∀ y ∈ u • (rootCenterIn J φ V.subtype : Set G), IsConj u y) {y : V}
    (hy : y ∈ involutionCosetNormalizer J φ V.subtype u) : IsConj u (u * y) := by
  have hS : (u * V.subtype y) • (rootCenterIn J φ V.subtype : Set G) ∈
      involutionCosets J φ V.subtype u := ⟨y, hy, rfl⟩
  rw [← conj_orbit_eq_involutionCosets V.subtype_injective ht huV q hcard hfixed] at hS
  obtain ⟨v, hv⟩ := hS
  have hmem : u * V.subtype y ∈ (u * V.subtype y) • (rootCenterIn J φ V.subtype : Set G) :=
    Set.mem_smul_set.mpr ⟨1, (rootCenterIn J φ V.subtype).one_mem,
      (smul_eq_mul _ _).trans (mul_one _)⟩
  rw [hv] at hmem
  obtain ⟨g, hg, hgy⟩ := hmem
  exact (hΔ g hg).trans (isConj_iff.mpr ⟨v, hgy⟩)

theorem mem_rootCenterIn_of_mem_hull (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) (ht : u ^ 2 = 1)
    (huV : ∀ v : V, u * (v : G) * u⁻¹ = (fieldInvolution J φ v : G))
    (hΔ : ∀ y ∈ u • (rootCenterIn J φ V.subtype : Set G), IsConj u y) {g : G}
    (hg : g ∈ involutionCosetHull J φ V.subtype u) (hg2 : orderOf g = 2) (hgu : ¬ IsConj u g) :
    g ∈ rootCenterIn J φ V.subtype := by
  obtain ⟨y, hy, rfl | rfl⟩ := (mem_involutionCosetHull_iff V.subtype_injective ht huV g).mp hg
  · have h2 : orderOf y = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hg2
    exact Subgroup.mem_map_of_mem V.subtype ((orderOf_eq_two_iff_mem_rootCenter φ y).mp h2).1
  · exact absurd (isConj_mul_of_mem_normalizer hcard hfixed ht huV hΔ hy) hgu

end Cosets

theorem exists_not_stabilize_conj_coset {G : Type*} [Group G] [Finite G] {K : Type*} [Field K]
    [Finite K] [CharP K 2] {J : HermitianForm 3 K} {q : ℕ} (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) {V : Subgroup G}
    (φ : hermitianUnipotentCoord J ≃* V) {u : G} (hu : orderOf u = 2)
    (huV : ∀ v : V, u * (v : G) * u⁻¹ = (fieldInvolution J φ v : G))
    {Q : Subgroup G} (hQ : rootCenterIn J φ V.subtype = Q) {D : Set G}
    (hDconj : ∀ g : G, ∀ y ∈ D, g * y * g⁻¹ ∈ D) (hD2 : ∀ y ∈ D, orderOf y = 2)
    (hQD : ∀ y ∈ Q, y ≠ 1 → y ∈ D) (hΔ : ∀ y ∈ u • (Q : Set G), IsConj u y)
    (hDu : ∀ y ∈ D, ¬ IsConj u y) {x : G}
    (hx : MulAut.conj x '' (u • (Q : Set G)) ⊆ (involutionCosetHull J φ V.subtype u : Set G)) :
    ∃ v : V, MulAut.conj (v : G) '' (MulAut.conj x '' (u • (Q : Set G))) ≠
      MulAut.conj x '' (u • (Q : Set G)) := by
  subst hQ
  set Q := rootCenterIn J φ V.subtype
  set W := involutionCosetHull J φ V.subtype u
  have ht : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have huQ : ∀ e ∈ Q, x * (u * e) * x⁻¹ ∈ W := fun e he =>
    hx ⟨u * e, Set.mem_smul_set.mpr ⟨e, he, rfl⟩, rfl⟩
  have hxu : x * u * x⁻¹ ∈ W := by
    have h := huQ 1 Q.one_mem
    rwa [mul_one] at h
  have hxQ : ∀ e ∈ Q, x * e * x⁻¹ ∈ Q := by
    intro e he
    by_cases he1 : e = 1
    · rw [he1, mul_one, mul_inv_cancel]
      exact Q.one_mem
    · have hxe : x * e * x⁻¹ = (x * u * x⁻¹)⁻¹ * (x * (u * e) * x⁻¹) := by group
      have hD : x * e * x⁻¹ ∈ D := hDconj x e (hQD e he he1)
      refine Cosets.mem_rootCenterIn_of_mem_hull hcard hfixed ht huV hΔ ?_ (hD2 _ hD) (hDu _ hD)
      rw [hxe]
      exact W.mul_mem (W.inv_mem hxu) (huQ e he)
  have hxQeq : MulAut.conj x '' (Q : Set G) = Q :=
    Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.mpr fun e he => hxQ e he)
      (Set.ncard_image_of_injective _ (MulAut.conj x).injective).ge
  have hS : MulAut.conj x '' (u • (Q : Set G)) = (x * u * x⁻¹) • (Q : Set G) := by
    rw [Set.image_smul_distrib, hxQeq, MulAut.conj_apply]
  obtain ⟨y, hy, hxy | hxy⟩ := (mem_involutionCosetHull_iff V.subtype_injective ht huV _).mp hxu
  · have h2 : orderOf y = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact (congrArg orderOf hxy).symm.trans ((MulEquiv.orderOf_eq (MulAut.conj x) u).trans hu)
    obtain ⟨hyE, hy1⟩ := (orderOf_eq_two_iff_mem_rootCenter φ y).mp h2
    have hyQ : V.subtype y ∈ Q := Subgroup.mem_map_of_mem V.subtype hyE
    have hy1' : V.subtype y ≠ 1 := fun h => hy1 (V.subtype_injective (h.trans (map_one _).symm))
    exact absurd (isConj_iff.mpr ⟨x, hxy⟩) (hDu _ (hQD _ hyQ hy1'))
  · rw [hS, hxy]
    exact involutionCosets_not_fixed V.subtype_injective ht huV q hcard hfixed _ ⟨y, hy, rfl⟩

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
