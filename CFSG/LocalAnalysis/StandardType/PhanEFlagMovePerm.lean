module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagAdapt
public import CFSG.LocalAnalysis.StandardType.PhanEFlagInv

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] {m : ℕ}

lemma q2cFM_permRk_succ {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : ℕ) (k : Fin n) :
    permRk σ a (k.val + 1) =
      permRk σ a k.val + (if (σ⁻¹ k).val < a then 1 else 0) := by
  classical
  unfold permRk
  have hunion : (Finset.univ.filter fun x : Fin n => x.val < a ∧ (σ x).val < k.val + 1) =
      (Finset.univ.filter fun x : Fin n => x.val < a ∧ (σ x).val < k.val) ∪
        (Finset.univ.filter fun x : Fin n => x.val < a ∧ σ x = k) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h2) with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, Fin.ext h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, rfl⟩)
      · exact ⟨h1, by omega⟩
      · exact ⟨h1, by simp⟩
  have hdisj : Disjoint
      (Finset.univ.filter fun x : Fin n => x.val < a ∧ (σ x).val < k.val)
      (Finset.univ.filter fun x : Fin n => x.val < a ∧ σ x = k) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    rw [hx'.2] at hx
    exact absurd hx.2 (lt_irrefl _)
  have hcard2 : (Finset.univ.filter fun x : Fin n => x.val < a ∧ σ x = k).card =
      (if (σ⁻¹ k).val < a then 1 else 0) := by
    by_cases h : (σ⁻¹ k).val < a
    · rw [if_pos h, Finset.card_eq_one]
      refine ⟨σ⁻¹ k, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hx => σ.injective (by rw [hx.2]; exact (Equiv.apply_symm_apply σ k).symm),
        fun hx => ⟨by rw [hx]; exact h, by rw [hx]; simp⟩⟩
    · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x - ⟨hx, hk⟩
      exact h (by rw [← hk]; simpa using hx)
  rw [hunion, Finset.card_union_of_disjoint hdisj, hcard2]

lemma q2cFM_card_fin_lt {n j : ℕ} (hj : j ≤ n) :
    (Finset.univ.filter fun x : Fin n => x.val < j).card = j := by
  rcases eq_or_lt_of_le hj with rfl | hj'
  · rw [Finset.filter_true_of_mem (fun x _ => x.isLt), Finset.card_univ, Fintype.card_fin]
  · have h : (Finset.univ.filter fun x : Fin n => x.val < j) =
        Finset.Iio (⟨j, hj'⟩ : Fin n) := by
      ext x
      simp [Finset.mem_Iio, Fin.lt_def]
    rw [h, Fin.card_Iio]

lemma q2cFM_adjSwap_inv {m : ℕ} (i : Fin m) : (adjSwap i)⁻¹ = adjSwap i := by
  rw [adjSwap]; exact Equiv.swap_inv _ _

lemma q2cFM_adjSwap_val_lt {m : ℕ} (i : Fin m) (y : Fin (m + 1)) {j : ℕ}
    (hj : j ≠ i.val + 1) : (adjSwap i y).val < j ↔ y.val < j := by
  unfold adjSwap
  rcases eq_or_ne y i.castSucc with h | h
  · subst h
    rw [Equiv.swap_apply_left]
    simp only [Fin.val_castSucc, Fin.val_succ]
    constructor <;> intro hh <;> omega
  · rcases eq_or_ne y i.succ with h' | h'
    · subst h'
      rw [Equiv.swap_apply_right]
      simp only [Fin.val_castSucc, Fin.val_succ]
      constructor <;> intro hh <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne h h']

lemma q2cFM_permRk_adjSwap_mul {m : ℕ} (i : Fin m) (σ : Equiv.Perm (Fin (m + 1)))
    (a j : ℕ) (hj : j ≠ i.val + 1) :
    permRk (adjSwap i * σ) a j = permRk σ a j := by
  unfold permRk
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x _
  rw [Equiv.Perm.mul_apply, q2cFM_adjSwap_val_lt i (σ x) hj]

lemma q2cFM_inv_adjSwap_mul_apply {m : ℕ} (i : Fin m) (σ : Equiv.Perm (Fin (m + 1))) :
    (adjSwap i * σ)⁻¹ i.castSucc = σ⁻¹ i.succ := by
  rw [mul_inv_rev, q2cFM_adjSwap_inv]
  simp only [Equiv.Perm.mul_apply]
  congr 1
  rw [adjSwap, Equiv.swap_apply_left]

lemma q2cFM_permRk_adjSwap_mul_succ {m : ℕ} (i : Fin m)
    (σ : Equiv.Perm (Fin (m + 1))) (a : ℕ) :
    permRk (adjSwap i * σ) a (i.val + 1) =
      permRk σ a i.val + (if (σ⁻¹ i.succ).val < a then 1 else 0) := by
  rw [show i.val + 1 = i.castSucc.val + 1 from rfl,
    q2cFM_permRk_succ (adjSwap i * σ) a i.castSucc,
    q2cFM_permRk_adjSwap_mul i σ a i.castSucc.val (by simp only [Fin.val_castSucc]; omega),
    q2cFM_inv_adjSwap_mul_apply i σ]
  simp only [Fin.val_castSucc]

lemma q2cFM_permRk_adjSwap_self {m : ℕ} (i : Fin m) {j : ℕ} (hj : j ≤ m + 1)
    (hji : j ≠ i.val + 1) : permRk (adjSwap i) j j = j := by
  unfold permRk
  have hset : (Finset.univ.filter fun x : Fin (m + 1) => x.val < j ∧ (adjSwap i x).val < j) =
      Finset.univ.filter fun x : Fin (m + 1) => x.val < j := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx; exact hx.1
    · intro hx; exact ⟨hx, (q2cFM_adjSwap_val_lt i x hji).mpr hx⟩
  rw [hset, q2cFM_card_fin_lt hj]

lemma q2cFM_adjSwap_ne_one {m : ℕ} (i : Fin m) : adjSwap i ≠ 1 := by
  intro h
  have h' := congrFun (congrArg DFunLike.coe h) i.castSucc
  simp only [adjSwap, Equiv.swap_apply_left, Equiv.Perm.coe_one, id_eq] at h'
  exact absurd (congrArg Fin.val h') (by simp [Fin.val_succ])

lemma q2cFM_ind_sum_zero {u v a : ℕ} (h : a ≤ min u v) :
    (if u < a then 1 else 0) + (if v < a then 1 else 0) = 0 := by
  rw [if_neg (by omega : ¬ u < a), if_neg (by omega : ¬ v < a), add_zero]

lemma q2cFM_ind_sum_one {u v a : ℕ} (h1 : min u v < a) (h2 : a ≤ max u v) :
    (if u < a then 1 else 0) + (if v < a then 1 else 0) = 1 := by
  rcases le_total u v with h | h
  · rw [if_pos (min_eq_left h ▸ h1), if_neg (by have := max_eq_right h; omega), add_zero]
  · rw [if_neg (by have := max_eq_left h; omega), if_pos (min_eq_right h ▸ h1), zero_add]

lemma q2cFM_ind_sum_two {u v a : ℕ} (h : max u v < a) :
    (if u < a then 1 else 0) + (if v < a then 1 else 0) = 2 := by
  have hu : u < a := by omega
  have hv : v < a := by omega
  rw [if_pos hu, if_pos hv]

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
