module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedHullSupplement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCoreCover

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem invertedHull_normal_supplement_reverse (K X C : Subgroup G)
    (hXK : X ≤ K) (hCK : C ≤ K) [(X.subgroupOf K).Normal]
    (hproduct : (K : Set G) = (X : Set G) * (C : Set G)) :
    (K : Set G) = (C : Set G) * (X : Set G) := by
  have hnorm : K ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mp inferInstance
  ext k
  constructor
  · intro hk
    rw [hproduct] at hk
    obtain ⟨x, hx, c, hc, rfl⟩ := hk
    have hcX : c⁻¹ * x * c ∈ X :=
      (Subgroup.mem_normalizer_iff''.mp (hnorm (hCK hc)) x).mp hx
    exact Set.mem_mul.mpr ⟨c, hc, c⁻¹ * x * c, hcX, by group⟩
  · rintro ⟨c, hc, x, hx, rfl⟩
    exact K.mul_mem (hCK hc) (hXK hx)

theorem invertedHull_right_commutator_subgroup_eq_native (U W : Subgroup G) :
    Subgroup.closure {c : G | ∃ a ∈ U, ∃ b ∈ W, c = a⁻¹ * b⁻¹ * a * b} = ⁅U, W⁆ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro c ⟨a, ha, b, hb, rfl⟩
    have hmem := (Subgroup.commutator_le.mp (le_rfl : ⁅U, W⁆ ≤ ⁅U, W⁆))
      a⁻¹ (U.inv_mem ha) b⁻¹ (W.inv_mem hb)
    change a⁻¹ * b⁻¹ * a * b ∈ ⁅U, W⁆
    simpa only [commutatorElement_def, inv_inv] using hmem
  · apply Subgroup.commutator_le.mpr
    intro a ha b hb
    apply Subgroup.subset_closure
    exact ⟨a⁻¹, U.inv_mem ha, b⁻¹, W.inv_mem hb, by
      simp only [commutatorElement_def, inv_inv]⟩

theorem invertedHull_right_commutator_mem (z : G) (S X C : Subgroup G)
    (hzX : z ∈ Subgroup.normalizer (X : Set G))
    (hC : C ≤ Subgroup.centralizer ({z} : Set G))
    (hproduct : (S : Set G) = (C : Set G) * (X : Set G))
    (h : G) (hh : h ∈ S) : z⁻¹ * h⁻¹ * z * h ∈ X := by
  have hh' : h ∈ (S : Set G) := hh
  rw [hproduct] at hh'
  obtain ⟨c, hc, x, hx, rfl⟩ := hh'
  have hcomm : c * z = z * c :=
    Subgroup.mem_centralizer_singleton_iff.mp (hC hc)
  have hfix : c⁻¹ * z * c = z := by rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
  have hsource : z⁻¹ * (c * x)⁻¹ * z * (c * x) = z⁻¹ * x⁻¹ * z * x := by
    calc
      z⁻¹ * (c * x)⁻¹ * z * (c * x) = z⁻¹ * x⁻¹ * (c⁻¹ * z * c) * x := by group
      _ = z⁻¹ * x⁻¹ * z * x := by rw [hfix]
  rw [hsource]
  exact X.mul_mem ((Subgroup.mem_normalizer_iff''.mp hzX x⁻¹).mp (X.inv_mem hx)) hx

theorem invertedHull_stabilizer_commutators (z : G) (hz : orderOf z = 2)
    (S X C : Subgroup G) (hzX : z ∈ Subgroup.normalizer (X : Set G))
    (hC : C ≤ Subgroup.centralizer ({z} : Set G))
    (hproduct : (S : Set G) = (C : Set G) * (X : Set G)) :
    ⁅Subgroup.zpowers z, S⁆ ≤ X ∧ ∀ h ∈ S, z⁻¹ * h⁻¹ * z * h ∈ X := by
  have hsource := invertedHull_right_commutator_mem z S X C hzX hC hproduct
  refine ⟨?_, hsource⟩
  apply Subgroup.commutator_le.mpr
  intro a ha h hh
  rcases involution_zpowers_elements hz ha with haone | haz
  · rw [haone]
    simpa only [commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]
      using X.one_mem
  · have hm := hsource h⁻¹ (S.inv_mem hh)
    have hzinv : z⁻¹ = z := inv_eq_self_of_orderOf_eq_two hz
    rw [haz]
    simpa only [commutatorElement_def, inv_inv, hzinv] using hm

variable [Finite G]

theorem invertedHull_ambient_solvable_supplement (L H : Subgroup G)
    [Group.IsSolvable L] (hstrong : fusionStronglyEmbedded (H.subgroupOf L))
    (z : G) (hzL : z ∈ L) (hzH : z ∈ H) (hz : orderOf z = 2) :
    ∃ X : Subgroup G, X ≤ H ⊓ L ∧ Odd (Nat.card X) ∧
      (X.subgroupOf (H ⊓ L)).Normal ∧
      (H ⊓ L : Set G) = (X : Set G) *
        (H ⊓ L ⊓ Subgroup.centralizer ({z} : Set G) : Set G) ∧
      ¬ Subgroup.normalizer (X : Set G) ⊓ L ≤ H := by
  let Q := H.subgroupOf L
  let zL : L := ⟨z, hzL⟩
  have hzLorder : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans hz
  obtain ⟨Y, hYQ, hYodd, hYnormal, hQproduct, hYescape⟩ :=
    solvable_strong_embedding_odd_centralizer_supplement Q hstrong zL hzH hzLorder
  let X := Y.map L.subtype
  have hXK : X ≤ H ⊓ L := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨hYQ hy, y.property⟩
  have hXodd : Odd (Nat.card X) := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact hYodd
  have hQnorm : Q ≤ Subgroup.normalizer (Y : Set L) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYQ).mp hYnormal
  have hKnorm : H ⊓ L ≤ Subgroup.normalizer (X : Set G) := by
    intro k hk
    exact Subgroup.le_normalizer_map L.subtype
      (Subgroup.mem_map_of_mem L.subtype (hQnorm (show (⟨k, hk.2⟩ : L) ∈ Q from hk.1)))
  have hXnormal : (X.subgroupOf (H ⊓ L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hKnorm
  refine ⟨X, hXK, hXodd, hXnormal, ?_, ?_⟩
  · ext k
    constructor
    · intro hk
      let kL : L := ⟨k, hk.2⟩
      have hm : kL ∈ (Q : Set L) := hk.1
      rw [hQproduct] at hm
      obtain ⟨y, hy, c, hc, heq⟩ := hm
      refine Set.mem_mul.mpr ⟨y, Subgroup.mem_map_of_mem L.subtype hy,
        c, ⟨⟨hc.1, c.property⟩, ?_⟩, congrArg Subtype.val heq⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc.2))
    · rintro ⟨x, hx, c, hc, rfl⟩
      exact (H ⊓ L).mul_mem (hXK hx) hc.1
  · intro hnormH
    apply hYescape
    intro y hy
    have hyX : (y : G) ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype hy)
    exact hnormH ⟨hyX, y.property⟩

end CFSG.ShultStronglyClosedTI
