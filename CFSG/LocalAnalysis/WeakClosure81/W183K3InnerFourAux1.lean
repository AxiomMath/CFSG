module

import CFSG.LocalAnalysis.WeakClosure81.W183K3Quasi
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.Open Subgroup

theorem w183k3_card_closure_pair {G : Type*} [Group G] [Finite G] {d f : G}
    (hd2 : d * d = 1) (hf2 : f * f = 1) (hdf : d * f = f * d)
    (hd1 : d ≠ 1) (hf1 : f ≠ 1) (hne : d ≠ f) :
    Nat.card (Subgroup.closure ({d, f} : Set G)) = 4 := by
  have hmem : ∀ x : G, x ∈ Subgroup.closure ({d, f} : Set G) ↔
      x = 1 ∨ x = d ∨ x = f ∨ x = d * f := by
    have hd' : ∀ y, d * (d * y) = y := fun y => by rw [← mul_assoc, hd2, one_mul]
    have hba : ∀ y, f * (d * y) = d * (f * y) := fun y => by
      rw [← mul_assoc, ← hdf, mul_assoc]
    have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
    have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
    intro x
    constructor
    · intro hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
      | one => exact Or.inl rfl
      | mul y z hy hz ihy ihz =>
          rcases ihy with rfl | rfl | rfl | rfl <;>
            rcases ihz with rfl | rfl | rfl | rfl <;>
            simp only [mul_assoc, hd2, hf2, hd', hba, hdf.symm, mul_one, one_mul,
              true_or, or_true]
      | inv y hy ihy =>
          rcases ihy with rfl | rfl | rfl | rfl <;>
            simp only [inv_one, hdi, hfi, mul_inv_rev, hdf.symm, true_or, or_true]
    · rintro (rfl | rfl | rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
  have hdf1 : d * f ≠ 1 := by
    intro h
    apply hne
    calc d = d * (f * f) := by rw [hf2, mul_one]
      _ = (d * f) * f := by rw [mul_assoc]
      _ = 1 * f := by rw [h]
      _ = f := one_mul f
  have hd_df : d ≠ d * f := by
    intro h
    exact hf1 (mul_left_cancel (by rw [mul_one]; exact h)).symm
  have hf_df : f ≠ d * f := by
    intro h
    exact hd1 (mul_right_cancel (by rw [one_mul]; exact h.symm))
  have hTcard : ({1, d, f, d * f} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hd1.symm, hf1.symm, hdf1.symm⟩),
        Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hne, hd_df⟩),
        Set.ncard_insert_of_notMem (by
          simp only [Set.mem_singleton_iff]
          exact hf_df),
        Set.ncard_singleton]
  have hsub : ({1, d, f, d * f} : Set G) ⊆ (Subgroup.closure ({d, f} : Set G) : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  have hfin : (Subgroup.closure ({d, f} : Set G) : Set G).Finite := Set.toFinite _
  have hle : ((Subgroup.closure ({d, f} : Set G) : Set G)).ncard ≤ 4 := by
    calc ((Subgroup.closure ({d, f} : Set G) : Set G)).ncard
        ≤ ({1, d, f, d * f} : Set G).ncard := by
          refine Set.ncard_le_ncard ?_ (Set.toFinite _)
          intro x hx
          rcases (hmem x).mp hx with h | h | h | h <;> simp [h]
      _ ≤ 4 := by omega
  have hge : 4 ≤ ((Subgroup.closure ({d, f} : Set G) : Set G)).ncard := by
    rw [← hTcard]
    exact Set.ncard_le_ncard hsub hfin
  change ((Subgroup.closure ({d, f} : Set G) : Set G)).ncard = 4
  exact le_antisymm hle hge

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
