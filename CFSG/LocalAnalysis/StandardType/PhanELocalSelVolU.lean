module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Set.Card.Arithmetic

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open Module

private lemma plh_ncard_translate_image {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] (T : Submodule K V) (c : V) :
    ((fun x : V => x + c) '' (T : Set V)).ncard = Nat.card K ^ finrank K T := by
  calc
    ((fun x : V => x + c) '' (T : Set V)).ncard = (T : Set V).ncard :=
      Set.ncard_image_of_injective _ (add_left_injective c)
    _ = Nat.card T := by
      rw [← Nat.card_coe_set_eq (T : Set V)]
      exact Nat.card_congr
        (Equiv.subtypeEquivProp (funext fun x => propext SetLike.mem_coe))
    _ = Nat.card K ^ finrank K T := Module.natCard_eq_pow_finrank

private lemma plh_ncard_coe_submodule {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] (U : Submodule K V) :
    (U : Set V).ncard = Nat.card K ^ finrank K U := by
  have h : (U : Set V).ncard = Nat.card U := by
    rw [← Nat.card_coe_set_eq (U : Set V)]
    exact Nat.card_congr
      (Equiv.subtypeEquivProp (funext fun x => propext SetLike.mem_coe))
  exact h.trans (Module.natCard_eq_pow_finrank (K := K) (V := U))

theorem exists_mem_notMem_affine_of_sum_lt {K V ι : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] (U : Submodule K V) (s : Finset ι) (T : ι → Submodule K V)
    (c : ι → V) (hT : ∀ i ∈ s, T i ≤ U) (hc : ∀ i ∈ s, c i ∈ U)
    (h : ∑ i ∈ s, Nat.card K ^ finrank K (T i) < Nat.card K ^ finrank K U) :
    ∃ u ∈ U, ∀ i ∈ s, u - c i ∉ T i := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  let A : ι → Set V := fun i => (fun x : V => x + c i) '' (T i : Set V)
  have hA : ∀ i, (A i).ncard = Nat.card K ^ finrank K (T i) := fun i =>
    plh_ncard_translate_image (T i) (c i)
  have hle : (⋃ i ∈ s, A i).ncard ≤ ∑ i ∈ s, Nat.card K ^ finrank K (T i) := by
    calc
      (⋃ i ∈ s, A i).ncard ≤ ∑ i ∈ s, (A i).ncard := Finset.set_ncard_biUnion_le s A
      _ = ∑ i ∈ s, Nat.card K ^ finrank K (T i) := Finset.sum_congr rfl fun i _ => hA i
  have hUcard := plh_ncard_coe_submodule U
  have hlt : (⋃ i ∈ s, A i).ncard < (U : Set V).ncard := by
    calc
      (⋃ i ∈ s, A i).ncard ≤ ∑ i ∈ s, Nat.card K ^ finrank K (T i) := hle
      _ < Nat.card K ^ finrank K U := h
      _ = (U : Set V).ncard := hUcard.symm
  obtain ⟨u, huU, hu⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard hlt (Set.finite_univ.subset (Set.subset_univ _))
  refine ⟨u, huU, fun i hi hmem => hu ?_⟩
  exact Set.mem_iUnion.2 ⟨i,
    Set.mem_iUnion.2 ⟨hi, ⟨u - c i, hmem, sub_add_cancel u (c i)⟩⟩⟩

theorem exists_mem_notMem_affine_of_sum_lt_exc {K V ι : Type*} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] (U : Submodule K V) (s : Finset ι)
    (T : ι → Submodule K V) (c : ι → V) (R : Finset V) (hT : ∀ i ∈ s, T i ≤ U)
    (hc : ∀ i ∈ s, c i ∈ U)
    (h : ∑ i ∈ s, Nat.card K ^ finrank K (T i) + R.card < Nat.card K ^ finrank K U) :
    ∃ u ∈ U, (∀ i ∈ s, u - c i ∉ T i) ∧ u ∉ R := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  let A : ι → Set V := fun i => (fun x : V => x + c i) '' (T i : Set V)
  have hA : ∀ i, (A i).ncard = Nat.card K ^ finrank K (T i) := fun i =>
    plh_ncard_translate_image (T i) (c i)
  have hAsub : ∀ i ∈ s, A i ⊆ (U : Set V) := by
    intro i hi x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact U.add_mem (hT i hi hy) (hc i hi)
  have hle : (⋃ i ∈ s, A i).ncard ≤ ∑ i ∈ s, Nat.card K ^ finrank K (T i) := by
    calc
      (⋃ i ∈ s, A i).ncard ≤ ∑ i ∈ s, (A i).ncard := Finset.set_ncard_biUnion_le s A
      _ = ∑ i ∈ s, Nat.card K ^ finrank K (T i) := Finset.sum_congr rfl fun i _ => hA i
  have hUcard := plh_ncard_coe_submodule U
  have hRcard : ((R.filter (· ∈ U) : Finset V) : Set V).ncard ≤ R.card := by
    rw [Set.ncard_coe_finset]
    exact Finset.card_filter_le R _
  have hBsub : (⋃ i ∈ s, A i) ∪ ((R.filter (· ∈ U) : Finset V) : Set V) ⊆ (U : Set V) := by
    intro x hx
    rcases (Set.mem_union x _ _).1 hx with hx | hx
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
      obtain ⟨hi, hxi⟩ := Set.mem_iUnion.1 hxi
      exact hAsub i hi hxi
    · rw [Finset.mem_coe, Finset.mem_filter] at hx
      exact hx.2
  have hB_ncard : ((⋃ i ∈ s, A i) ∪ ((R.filter (· ∈ U) : Finset V) : Set V)).ncard ≤
      (∑ i ∈ s, Nat.card K ^ finrank K (T i)) + R.card := by
    have h1 : ((⋃ i ∈ s, A i) ∪
        ((R.filter (· ∈ U) : Finset V) : Set V)).ncard ≤
        (⋃ i ∈ s, A i).ncard + ((R.filter (· ∈ U) : Finset V) : Set V).ncard :=
      Set.ncard_union_le _ _
    exact le_trans h1 (add_le_add hle hRcard)
  have hlt : ((⋃ i ∈ s, A i) ∪
      ((R.filter (· ∈ U) : Finset V) : Set V)).ncard < (U : Set V).ncard := by
    calc
      ((⋃ i ∈ s, A i) ∪ ((R.filter (· ∈ U) : Finset V) : Set V)).ncard ≤
          (∑ i ∈ s, Nat.card K ^ finrank K (T i)) + R.card := hB_ncard
      _ < Nat.card K ^ finrank K U := h
      _ = (U : Set V).ncard := hUcard.symm
  obtain ⟨u, huU, huB⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard hlt (Set.finite_univ.subset (Set.subset_univ _))
  refine ⟨u, huU, fun i hi hmem => ?_, fun huR => ?_⟩
  · exact huB (Or.inl (Set.mem_iUnion.2 ⟨i,
      Set.mem_iUnion.2 ⟨hi, ⟨u - c i, hmem, sub_add_cancel u (c i)⟩⟩⟩))
  · exact huB (Or.inr (by
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨huR, huU⟩))

end CFSG.ClassicalInvolution.Phan.PhanE

end
