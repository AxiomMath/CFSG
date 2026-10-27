module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedProduct

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryHulls CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ShultStronglyClosedTI.ProperPairModel CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {z : G} {beta : rightCosetSpace H}
  {t u : G} {A P : Subgroup G}

theorem mem_normalizer_root_of_mem {L : Subgroup G} (F : UnitaryHullCoordinates H z beta t L)
    {p : G} (hpH : p ∈ H) (hpL : p ∈ Subgroup.normalizer (L : Set G)) :
    p ∈ Subgroup.normalizer (F.root : Set G) := by
  refine mem_normalizer_of_map_le ?_
  rintro _ ⟨τ, hτ, rfl⟩
  change p * τ * p⁻¹ ∈ F.root
  refine mem_root_of_pow_eq_one F ((Subgroup.mem_normalizer_iff.mp hpL τ).mp (F.root_le hτ))
    (H.mul_mem (H.mul_mem hpH (F.root_le_point hτ)) (H.inv_mem hpH)) (k := 2) ?_
  obtain ⟨w, rfl⟩ := hτ
  rw [conj_pow, ← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, pow_four_eq_one, map_one, mul_one,
    mul_inv_cancel]

namespace ExclusionSetup

variable (d : ExclusionSetup H z beta t u A P)
include d

omit [Finite G] in
theorem P_le_H : P ≤ H := d.P_le.trans (pairPointStabilizer_le_point H beta)

omit [Finite G] in
theorem P_commute_u {p : G} (hp : p ∈ P) : p * u = u * p :=
  Subgroup.mem_centralizer_singleton_iff.mp (d.P_commute hp)

omit [Finite G] in
theorem P_le_normalizer_point :
    P ≤ Subgroup.normalizer (minimalLocalFailurePairActionPointHull H z : Set G) := by
  intro p hp
  have hpH := d.P_le_H hp
  refine Subgroup.mem_normalizer_iff.mpr fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · have h := point_subgroup_normalized d.point_class p⁻¹ (H.inv_mem hpH) q hq
    rwa [inv_inv] at h
  · have h := point_subgroup_normalized d.point_class p hpH _ hq
    rwa [show p⁻¹ * (p * q * p⁻¹) * p = q by group] at h

omit [Finite G] in
theorem P_le_normalizer_coset :
    P ≤ Subgroup.normalizer (u • (minimalLocalFailurePairActionPointHull H z : Set G)) := by
  intro p hp
  have hQ := d.P_le_normalizer_point hp
  have hpu : Commute p u := d.P_commute_u hp
  refine Subgroup.mem_set_normalizer_iff.mpr fun y => ⟨?_, ?_⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨p * q * p⁻¹, (Subgroup.mem_normalizer_iff.mp hQ q).mp hq, ?_⟩
    change u * (p * q * p⁻¹) = p * (u * q) * p⁻¹
    rw [show p * (u * q) * p⁻¹ = p * u * q * p⁻¹ by group, hpu.eq]
    group
  · rintro ⟨q, hq, hqy⟩
    change u * q = p * y * p⁻¹ at hqy
    refine ⟨p⁻¹ * q * p, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hQ (p⁻¹ * q * p)).mpr
        (by rwa [show p * (p⁻¹ * q * p) * p⁻¹ = q by group])
    · change u * (p⁻¹ * q * p) = y
      have hy : y = p⁻¹ * u * q * p := by
        rw [mul_assoc p⁻¹ u q, hqy]
        group
      rw [hy, hpu.inv_left.eq]
      group

omit [Finite G] in
theorem P_le_normalizer_Lu : P ≤ Subgroup.normalizer (uHull z u : Set G) := fun _ hp =>
  mem_normalizer_uHull (d.P_commute_u hp)

omit [Finite G] in
theorem P_le_normalizer_pairHull :
    P ≤ Subgroup.normalizer (minimalLocalFailureProperPairHull H z beta t : Set G) :=
  d.P_le.trans d.pair_normalizes

theorem P_le_normalizer_torus : P ≤ Subgroup.normalizer (hullTorus d.Fu : Set G) := by
  intro p hp
  rw [← inf_centralizer_pairHull d.Fu d.datum d.flip_coset d.flip_sq]
  refine mem_normalizer_of_map_le ?_
  rintro _ ⟨x, ⟨hxL, hxK⟩, rfl⟩
  exact ⟨(Subgroup.mem_normalizer_iff.mp (d.P_le_normalizer_Lu hp) x).mp hxL,
    (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_centralizer (d.P_le_normalizer_pairHull hp)) x).mp hxK⟩

theorem P_le_normalizer_A : P ≤ Subgroup.normalizer (A : Set G) := fun _ hp =>
  mem_normalizer_of_le_isCyclic d.A_le_torus (hullTorus_isCyclic_odd d.Fu).1
    (d.P_le_normalizer_torus hp)

theorem P_le_normalizer_LA : P ≤ Subgroup.normalizer (aHull z A : Set G) := by
  intro p hp
  have hpC := mem_normalizer_centralizer (d.P_le_normalizer_A hp)
  have hcS : p ∈ Subgroup.normalizer
      (involutionPointClass z ∩ (Subgroup.centralizer (A : Set G) : Set G)) := by
    refine Subgroup.mem_set_normalizer_iff.mpr fun y => ⟨?_, ?_⟩
    · rintro ⟨⟨k, rfl⟩, hy⟩
      refine ⟨⟨k * p⁻¹, ?_⟩, (Subgroup.mem_normalizer_iff.mp hpC _).mp hy⟩
      simp only [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem]
      group
    · rintro ⟨⟨k, hk⟩, hy⟩
      refine ⟨⟨k * p, ?_⟩, (Subgroup.mem_normalizer_iff.mp hpC _).mpr hy⟩
      simp only [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem] at hk ⊢
      rw [show (k * p)⁻¹ * z * (k * p) = p⁻¹ * (k⁻¹ * z * k) * p by group, hk]
      group
  exact Subgroup.normalizer_le_normalizer_closure _ hcS

theorem P_le_normalizer_rootU : P ≤ Subgroup.normalizer (d.Fu.root : Set G) := fun _ hp =>
  mem_normalizer_root_of_mem d.Fu (d.P_le_H hp) (d.P_le_normalizer_Lu hp)

theorem P_le_normalizer_rootA : P ≤ Subgroup.normalizer (d.FA.root : Set G) := fun _ hp =>
  mem_normalizer_root_of_mem d.FA (d.P_le_H hp) (d.P_le_normalizer_LA hp)

end ExclusionSetup

namespace BarCoordinates

variable {d : ExclusionSetup H z beta t u A P} (b : BarCoordinates d)

omit [Finite G] in
theorem mem_U_iff {x : G} : x ∈ b.U ↔ x ∈ d.FA.root ∧
    x ∈ Subgroup.normalizer (u • (minimalLocalFailurePairActionPointHull H z : Set G)) := by
  refine ⟨fun hx => ⟨b.U_le_root hx, b.U_le_normalizer hx⟩, fun ⟨hxV, hxΔ⟩ => ?_⟩
  refine ⟨⟨x, hxV⟩, ?_, rfl⟩
  change x ∈ Subgroup.normalizer (involutionCoset d.FA.J b.φ d.FA.root.subtype u)
  rwa [b.coset_eq]

theorem P_le_normalizer_U : P ≤ Subgroup.normalizer (b.U : Set G) := by
  intro p hp
  refine mem_normalizer_of_map_le ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hxV, hxΔ⟩ := (b.mem_U_iff).mp hx
  have hpΔ := d.P_le_normalizer_coset hp
  refine (b.mem_U_iff).mpr ⟨(Subgroup.mem_normalizer_iff.mp
    (d.P_le_normalizer_rootA hp) x).mp hxV, ?_⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hpΔ hxΔ) (Subgroup.inv_mem _ hpΔ)

theorem P_le_normalizer_W : P ≤ Subgroup.normalizer (b.W : Set G) := by
  intro p hp
  refine mem_normalizer_of_map_le ?_
  rintro _ ⟨w, hw, rfl⟩
  change p * w * p⁻¹ ∈ b.W
  have hU := Subgroup.mem_normalizer_iff.mp (b.P_le_normalizer_U hp)
  obtain ⟨x, hx, h | h⟩ := (b.mem_W_iff w).mp hw <;> rw [h]
  · exact b.U_le_W ((hU x).mp hx)
  · rw [show p * (u * x) * p⁻¹ = p * u * x * p⁻¹ by group, d.P_commute_u hp,
      show u * p * x * p⁻¹ = u * (p * x * p⁻¹) by group]
    exact Subgroup.mul_mem _ b.u_mem_W (b.U_le_W ((hU x).mp hx))

theorem P_le_normalizer_S : P ≤ Subgroup.normalizer ((d.Fu.root ⊔ b.W : Subgroup G) : Set G) := by
  intro p hp
  refine mem_normalizer_of_map_le ?_
  rw [Subgroup.map_sup]
  refine sup_le_sup ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (d.P_le_normalizer_rootU hp) x).mp hx
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (b.P_le_normalizer_W hp) x).mp hx

theorem S_inf_P : (d.Fu.root ⊔ b.W) ⊓ P = Subgroup.zpowers u := by
  refine le_antisymm ?_ ?_
  · rintro s ⟨hsS, hsP⟩
    rcases b.eq_one_or_eq_u hsS (d.P_le hsP) with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact ⟨Subgroup.mem_sup_right b.u_mem_W, d.u_mem_P⟩

theorem card_X : Nat.card ((d.Fu.root ⊔ b.W) ⊔ P : Subgroup G) =
    Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 4 * Nat.card P := by
  have h := card_sup_mul_card_inf b.P_le_normalizer_S
  rw [b.S_inf_P, Nat.card_zpowers, d.u_order, b.card_S] at h
  refine Nat.eq_of_mul_eq_mul_right two_pos ?_
  rw [h]
  ring

end BarCoordinates

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
