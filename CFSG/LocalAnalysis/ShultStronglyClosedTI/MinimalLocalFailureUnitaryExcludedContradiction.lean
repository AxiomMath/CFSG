module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureMixedClassBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedCosets

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

theorem degree_eq {q : ℕ} (hq : 1 ≤ q) :
    (q ^ 3 + 1) * (q ^ 3 * (q - 1) + 1) = q ^ 4 * (q ^ 3 - q ^ 2 + 1) + 1 := by
  have h2 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hq (by norm_num)
  zify [hq, h2]
  ring

namespace ExclusionSetup

variable (d : ExclusionSetup H z beta t u A P)
include d

omit [Finite G] d in
theorem class_conj (g : G) {y : G} (hy : y ∈ involutionPointClass z) :
    g * y * g⁻¹ ∈ involutionPointClass z := by
  obtain ⟨k, rfl⟩ := hy
  refine ⟨k * g⁻¹, ?_⟩
  simp only [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem]
  group

omit [Finite G] in
theorem class_order {y : G} (hy : y ∈ involutionPointClass z) : orderOf y = 2 :=
  order_two_of_mem_pointClass d.datum.distinguished_order hy

omit [Finite G] in
theorem point_mem_class {y : G} (hy : y ∈ minimalLocalFailurePairActionPointHull H z)
    (hy1 : y ≠ 1) : y ∈ involutionPointClass z :=
  point_subgroup_class d.datum d.point_class ⟨hy, hy1⟩

omit [Finite G] in
theorem coset_isConj {y : G} (hy : y ∈ u • (minimalLocalFailurePairActionPointHull H z : Set G)) :
    IsConj u y :=
  MixedClass.mem_pointClass_iff_isConj.mp (d.coset_class hy)

omit [Finite G] in
theorem class_not_isConj {y : G} (hy : y ∈ involutionPointClass z) : ¬ IsConj u y := fun h =>
  d.u_not_conj ((MixedClass.mem_pointClass_iff_isConj.mp hy).trans h.symm)

end ExclusionSetup

namespace BarCoordinates

variable {d : ExclusionSetup H z beta t u A P} (b : BarCoordinates d)

theorem index_odd : ¬ 2 ∣ ((d.Fu.root ⊔ b.W) ⊔ P : Subgroup G).index := by
  have hq1 : 1 ≤ Nat.card (minimalLocalFailurePairActionPointHull H z) := Nat.card_pos
  have hqeven : Even (Nat.card (minimalLocalFailurePairActionPointHull H z)) := by
    rw [d.Fu.hq]
    exact (Nat.even_pow' (by have := d.Fu.hf; omega)).mpr even_two
  have hn := d.degree.trans (degree_eq hq1)
  have hBidx : (pairPointStabilizer H beta).relIndex H =
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 4 *
        (Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 -
          Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 + 1) := by
    rw [d.pair_index, hn, Nat.add_sub_cancel]
  have hH : (pairPointStabilizer H beta).relIndex H * Nat.card (pairPointStabilizer H beta) =
      Nat.card H := by
    have h := Subgroup.relIndex_mul_card (pairPointStabilizer H beta) H
    rwa [inf_of_le_left (pairPointStabilizer_le_point H beta)] at h
  have hB : P.relIndex (pairPointStabilizer H beta) * Nat.card P =
      Nat.card (pairPointStabilizer H beta) := by
    have h := Subgroup.relIndex_mul_card P (pairPointStabilizer H beta)
    rwa [inf_of_le_left d.P_le] at h
  have hXG := Subgroup.index_mul_card ((d.Fu.root ⊔ b.W) ⊔ P : Subgroup G)
  rw [b.card_X] at hXG
  have key : ((d.Fu.root ⊔ b.W) ⊔ P : Subgroup G).index *
      (Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 4 * Nat.card P) =
      Nat.card (rightCosetSpace H) *
        (Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 -
          Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 + 1) *
        P.relIndex (pairPointStabilizer H beta) *
        (Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 4 * Nat.card P) := by
    rw [hXG, ← H.index_mul_card, ← MixedClass.card_rightCosetSpace H, ← hH, ← hB, hBidx]
    ring
  have hpos : 0 < Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 4 * Nat.card P :=
    Nat.mul_pos (pow_pos hq1 4) Nat.card_pos
  rw [Nat.eq_of_mul_eq_mul_right hpos key]
  have hm : Odd (Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 -
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 + 1) := by
    have h3 := hqeven.pow_of_ne_zero (n := 3) (by norm_num)
    have h2 := hqeven.pow_of_ne_zero (n := 2) (by norm_num)
    exact ((Nat.even_sub (Nat.pow_le_pow_right hq1 (by norm_num))).mpr
      ⟨fun _ => h2, fun _ => h3⟩).add_one
  have hnodd : Odd (Nat.card (rightCosetSpace H)) := by
    rw [hn]
    exact ((hqeven.pow_of_ne_zero (by norm_num : 4 ≠ 0)).mul_right _).add_one
  have hPodd : Odd (P.relIndex (pairPointStabilizer H beta)) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp d.P_index)
  intro h2
  exact (Nat.not_even_iff_odd.mpr ((hnodd.mul hm).mul hPodd)) (even_iff_two_dvd.mpr h2)

include b in
theorem false : False := by
  set Δ := u • (minimalLocalFailurePairActionPointHull H z : Set G)
  have hXN : (d.Fu.root ⊔ b.W) ⊔ P ≤ Subgroup.normalizer (b.W : Set G) :=
    sup_le b.S_le_normalizer_W b.P_le_normalizer_W
  have hX2 : IsPGroup 2 ((d.Fu.root ⊔ b.W) ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' b.S_isPGroup d.P_two b.P_le_normalizer_S
  have hXΔ : (d.Fu.root ⊔ b.W) ⊔ P ≤ Subgroup.normalizer Δ :=
    sup_le b.S_le_normalizer_coset d.P_le_normalizer_coset
  obtain ⟨g, hgN, hg⟩ := exists_conj_le_of_not_two_dvd_index hXN hX2 b.index_odd
    b.root_sup_le_normalizer b.root_sup_isPGroup
  have hΔW : Δ ⊆ (b.W : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.mul_mem _ b.u_mem_W (b.U_le_W (b.point_le_U hq))
  have hsub : MulAut.conj g⁻¹ '' Δ ⊆ (b.W : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) y).mp (hΔW hy)
    change g⁻¹ * y * g⁻¹⁻¹ ∈ b.W
    exact h
  obtain ⟨v, hv⟩ := exists_not_stabilize_conj_coset d.FA.hcard d.FA.hfixed b.φ d.u_order
    b.bar_field b.center_eq (fun g _ hy => ExclusionSetup.class_conj g hy)
    (fun _ hy => d.class_order hy)
    (fun _ hy hy1 => d.point_mem_class hy hy1) (fun _ hy => d.coset_isConj hy)
    (fun _ hy => d.class_not_isConj hy) hsub
  apply hv
  have hgv : g * (v : G) * g⁻¹ ∈ Subgroup.normalizer Δ :=
    hXΔ (hg ⟨v, Subgroup.mem_sup_left v.2, rfl⟩)
  have himg := Subgroup.mem_normalizer_iff_conj_image_eq.mp hgv
  calc MulAut.conj (v : G) '' (MulAut.conj g⁻¹ '' Δ) =
        MulAut.conj g⁻¹ '' (MulAut.conj (g * (v : G) * g⁻¹) '' Δ) := by
        rw [Set.image_image, Set.image_image]
        congr 1
        funext y
        simp only [MulAut.conj_apply]
        group
    _ = MulAut.conj g⁻¹ '' Δ := by rw [himg]

end BarCoordinates

theorem ExclusionSetup.false (d : ExclusionSetup H z beta t u A P) : False := by
  obtain ⟨b⟩ := d.nonempty_barCoordinates
  exact b.false

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
