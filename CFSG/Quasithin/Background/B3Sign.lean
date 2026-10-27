module

public import CFSG.Quasithin.Background.B3Vec
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.B3

@[expose] def invCount (t : Tab) : ℕ :=
  ((List.range t.length).map (fun i =>
    ((List.range t.length).filter
      (fun j => decide (i < j) && decide (t.getD j 0 < t.getD i 0))).length)).sum

@[expose] def isEvenT (t : Tab) : Bool := invCount t % 2 == 0

theorem invCount_tab {n : ℕ} (σ : Gp n) :
    invCount (tab σ) = ∑ i : Fin n, ∑ j : Fin n, (if i < j ∧ σ j < σ i then 1 else 0) := by
  unfold invCount
  rw [length_tab, list_sum_range]
  have h1 : ∀ i : ℕ, ((List.range n).filter
      (fun j => decide (i < j) && decide ((tab σ).getD j 0 < (tab σ).getD i 0))).length
      = ∑ j ∈ Finset.range n, (if (decide (i < j) &&
          decide ((tab σ).getD j 0 < (tab σ).getD i 0)) = true then 1 else 0) :=
    fun i => length_filter_range _ n
  simp_rw [h1]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, (if (decide (i < j) &&
    decide ((tab σ).getD j 0 < (tab σ).getD i 0)) = true then 1 else 0)) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => (if (decide ((i : ℕ) < j) &&
    decide ((tab σ).getD j 0 < (tab σ).getD i 0)) = true then 1 else 0)) n]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [getD_tab, getD_tab]
  simp only [Fin.val_fin_lt, Bool.and_eq_true, decide_eq_true_eq]

theorem sign_eq_pow_invCount {n : ℕ} (σ : Gp n) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ invCount (tab σ) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi, invCount_tab]
  have h1 : ∀ i : Fin n, ∏ j ∈ Finset.Ioi i, (if σ i < σ j then (1 : ℤˣ) else -1)
      = (-1 : ℤˣ) ^ (∑ j : Fin n, if i < j ∧ σ j < σ i then 1 else 0) := by
    intro i
    have h2 : ∀ j ∈ Finset.Ioi i, (if σ i < σ j then (1 : ℤˣ) else -1)
        = (-1 : ℤˣ) ^ (if i < j ∧ σ j < σ i then 1 else 0) := by
      intro j hj
      have hij : i < j := Finset.mem_Ioi.1 hj
      have hne : σ i ≠ σ j := fun h => (ne_of_lt hij) (σ.injective h)
      by_cases h : σ i < σ j
      · have : ¬ σ j < σ i := not_lt.2 h.le
        simp [h, hij, this]
      · have : σ j < σ i := lt_of_le_of_ne (not_lt.1 h) (Ne.symm hne)
        simp [h, hij, this]
    rw [Finset.prod_congr rfl h2, Finset.prod_pow_eq_pow_sum]
    congr 1
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have : ¬ i < j := fun h => hj (Finset.mem_Ioi.2 h)
    simp [this]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_pow_eq_pow_sum]

theorem mem_alternatingGroup_iff {n : ℕ} (σ : Gp n) :
    σ ∈ alternatingGroup (Fin n) ↔ isEvenT (tab σ) = true := by
  rw [Equiv.Perm.mem_alternatingGroup, sign_eq_pow_invCount, isEvenT, beq_iff_eq]
  have h : (-1 : ℤˣ) ≠ 1 := by decide
  rw [neg_one_pow_eq_one_iff_even h, Nat.even_iff]

end CFSG.Quasithin.B3
