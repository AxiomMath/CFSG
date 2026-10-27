module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedBar
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedCommutator

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryHulls CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

variable {G : Type} [Group G] {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t u : G}
  {A P : Subgroup G} {d : ExclusionSetup H z beta t u A P}

theorem mem_normalizer_of_map_le [Finite G] {K : Subgroup G} {g : G}
    (h : K.map (MulAut.conj g).toMonoidHom ≤ K) : g ∈ Subgroup.normalizer (K : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge h (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge)

theorem ExclusionSetup.u_centralizes_coset (d : ExclusionSetup H z beta t u A P) :
    u ∈ Subgroup.centralizer (u • (minimalLocalFailurePairActionPointHull H z : Set G)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨q, hq, rfl⟩
  have hq' := Subgroup.mem_centralizer_singleton_iff.mp (d.u_point hq)
  change u * q * u = u * (u * q)
  rw [mul_assoc, hq']

namespace BarCoordinates

variable (b : BarCoordinates d)

@[expose] def U : Subgroup G :=
  (involutionCosetNormalizer d.FA.J b.φ d.FA.root.subtype u).map d.FA.root.subtype

@[expose] def W : Subgroup G :=
  involutionCosetHull d.FA.J b.φ d.FA.root.subtype u

theorem U_le_root : b.U ≤ d.FA.root := by
  rintro _ ⟨v, -, rfl⟩
  exact v.2

theorem U_le_aHull : b.U ≤ aHull z A := (b.U_le_root).trans (d.FA.root_le)

theorem U_le_centralizer_A : b.U ≤ Subgroup.centralizer (A : Set G) :=
  b.U_le_aHull.trans (aHull_le_centralizer z A)

theorem U_le_centralizer_point :
    b.U ≤ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) :=
  fun _ hx => Subgroup.mem_centralizer_iff.mpr fun _ hq =>
    (root_commute d.FA (b.U_le_root hx) hq).symm

theorem U_le_normalizer :
    b.U ≤ Subgroup.normalizer (u • (minimalLocalFailurePairActionPointHull H z : Set G)) := by
  rintro _ ⟨v, hv, rfl⟩
  have h : d.FA.root.subtype v ∈ Subgroup.normalizer
      (involutionCoset d.FA.J b.φ d.FA.root.subtype u) := hv
  rwa [b.coset_eq] at h

theorem point_le_U : minimalLocalFailurePairActionPointHull H z ≤ b.U := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := (SetLike.ext_iff.mp b.center_eq x).mpr hx
  refine ⟨v, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_involutionCosetNormalizer Subtype.val_injective d.u_sq b.bar_field]
  rw [SetLike.mem_coe, mem_rootCenter] at hv
  rw [hv, map_zero]

theorem U_le_W : b.U ≤ b.W := le_sup_left

theorem u_mem_W : u ∈ b.W := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)

theorem card_U : Nat.card b.U = (2 ^ d.FA.f) ^ 2 := by
  rw [U, Subgroup.card_map_of_injective Subtype.val_injective]
  exact card_involutionCosetNormalizer Subtype.val_injective d.u_sq b.bar_field _ d.FA.hcard
    d.FA.hfixed

theorem mem_point_of_mul_self {x : G} (hx : x ∈ b.U) (hx2 : x * x = 1) :
    x ∈ minimalLocalFailurePairActionPointHull H z := by
  obtain ⟨v, -, rfl⟩ := hx
  by_cases hv : v = 1
  · rw [hv, map_one]
    exact Subgroup.one_mem _
  · have hv2 : orderOf v = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime ?_ hv
      apply Subtype.val_injective
      rw [Subgroup.coe_pow, pow_two]
      exact hx2
    exact (SetLike.ext_iff.mp b.center_eq _).mp
      ⟨v, ((orderOf_eq_two_iff_mem_rootCenter b.φ v).mp hv2).1, rfl⟩

theorem conj_U {x : G} (hx : x ∈ b.U) : u * x * u⁻¹ = x⁻¹ := by
  obtain ⟨v, hv, rfl⟩ := hx
  rw [conj_eq_inv Subtype.val_injective d.u_sq b.bar_field hv, map_inv]

theorem mem_W_iff (g : G) : g ∈ b.W ↔ ∃ x ∈ b.U, g = x ∨ g = u * x := by
  rw [W, mem_involutionCosetHull_iff Subtype.val_injective d.u_sq b.bar_field]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, ⟨v, hv, rfl⟩, h⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, h⟩
    exact ⟨v, hv, h⟩

theorem card_W : Nat.card b.W = 2 * (2 ^ d.FA.f) ^ 2 :=
  card_involutionCosetHull Subtype.val_injective d.u_sq b.bar_field _ d.FA.hcard d.FA.hfixed

theorem W_isPGroup : IsPGroup 2 b.W := fun w =>
  ⟨2, Subtype.ext (by
    rw [Subgroup.coe_pow, show 2 ^ 2 = 4 by norm_num,
      pow_four_eq_one_of_mem_hull Subtype.val_injective d.u_sq b.bar_field w.2,
      Subgroup.coe_one])⟩

theorem W_le_normalizer :
    b.W ≤ Subgroup.normalizer (u • (minimalLocalFailurePairActionPointHull H z : Set G)) :=
  sup_le b.U_le_normalizer (Subgroup.zpowers_le.mpr
    (Subgroup.centralizer_le_normalizer _ d.u_centralizes_coset))

theorem root_sup_le_normalizer :
    d.FA.root ⊔ Subgroup.zpowers u ≤ Subgroup.normalizer (b.W : Set G) := by
  have h := le_normalizer_involutionCosetHull (ι := d.FA.root.subtype) Subtype.val_injective
    d.u_sq b.bar_field
  rwa [Subgroup.range_subtype] at h

include b in
theorem root_sup_isPGroup [Finite G] :
    IsPGroup 2 (d.FA.root ⊔ Subgroup.zpowers u : Subgroup G) := by
  have hu : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers (k := 1) (by
    rw [pow_one]
    exact d.u_sq)
  refine IsPGroup.to_sup_of_normal_left' (ExclusionSetup.root_isPGroup d.FA) hu ?_
  rw [Subgroup.zpowers_le]
  refine mem_normalizer_of_map_le fun _ ⟨v, hv, hvx⟩ => ?_
  rw [← hvx]
  have h := b.bar_field ⟨v, hv⟩
  change u * v * u⁻¹ ∈ d.FA.root
  rw [h]
  exact (fieldInvolution d.FA.J b.φ ⟨v, hv⟩).2

end BarCoordinates

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
