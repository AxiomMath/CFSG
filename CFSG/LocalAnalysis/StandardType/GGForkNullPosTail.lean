module

public import CFSG.LocalAnalysis.StandardType.GGForkNullPos

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Tail

variable {Λ : Type} [Fintype Λ] [DecidableEq Λ]

theorem ggAttachNullPos_false_of_tail {Λ' : Type} [Fintype Λ'] [DecidableEq Λ']
    (C : Matrix Λ Λ ℤ) (k : Λ) (hneg : ∀ i j, i ≠ j → C i j ≤ 0) (C' : Matrix Λ' Λ' ℤ) (k' : Λ')
    (σ : Λ' ↪ Λ) (hσ : ∀ i j, C (σ i) (σ j) = C' i j) (hk : k = σ k') (y' : Option Λ' → ℤ)
    (hy' : ∀ i, y' i ≤ 0)
    (h1 : ∀ i, 0 ≤ ∑ j, ggAttachCartan C' k' i j * y' j)
    (h2 : ∃ i, 0 < ∑ j, ggAttachCartan C' k' i j * y' j) : ¬ GGAttachNullPos C k := by
  classical
  let e : Option Λ' ↪ Option Λ := Function.Embedding.optionMap σ
  let y : Option Λ → ℤ := Function.extend e y' 0
  have he_none : e none = none := rfl
  have he_some (x : Λ') : e (some x) = some (σ x) := rfl
  have hy_apply (x : Option Λ') : y (e x) = y' x :=
    Function.Injective.extend_apply e.injective y' 0 x
  have hy_apply' (j : Option Λ) (hj : j ∉ Set.range e) : y j = 0 :=
    Function.extend_apply' (f := e) y' 0 j (by simpa [Set.mem_range] using hj)
  have key : ∀ (i' l : Option Λ'), ggAttachCartan C k (e i') (e l) = ggAttachCartan C' k' i' l := by
    intro i' l
    rcases i' with _ | i₁ <;> rcases l with _ | l₁
    · simp [he_none]
    · simp only [he_none, he_some, ggAttachCartan_none_some]
      rw [hk]
      simp only [Function.Embedding.apply_eq_iff_eq]
    · simp only [he_none, he_some, ggAttachCartan_some_none]
      rw [hk]
      simp only [Function.Embedding.apply_eq_iff_eq]
    · simp only [he_some, ggAttachCartan_some_some]
      exact hσ i₁ l₁
  have hsum (i : Option Λ) :
      ∑ j, ggAttachCartan C k i j * y j =
        ∑ l : Option Λ', ggAttachCartan C k i (e l) * y' l := by
    have hsub : ∑ j ∈ Finset.univ.image e, ggAttachCartan C k i j * y j =
        ∑ j, ggAttachCartan C k i j * y j := by
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro j _ hj
      rw [hy_apply' j (by simpa [Finset.mem_image, Set.mem_range] using hj), mul_zero]
    rw [← hsub, Finset.sum_image (fun x _ y _ h => e.injective h)]
    apply Finset.sum_congr rfl
    intro l _
    rw [hy_apply]
  have hX : ∀ (i : Option Λ) (l : Option Λ'), (∀ i', e i' ≠ i) →
      ggAttachCartan C k i (e l) ≤ 0 := by
    intro i l hi
    rcases i with _ | i₁
    · exact absurd he_none (hi none)
    · rcases l with _ | l₁
      · rw [he_none, ggAttachCartan_some_none]
        split <;> omega
      · rw [he_some, ggAttachCartan_some_some]
        apply hneg
        intro h
        exact hi (some l₁) (by rw [he_some, h])
  refine ggAttachNullPos_false_of_cert C k y ?_ ?_
  · intro i
    rw [hsum i]
    by_cases hi : ∃ i', e i' = i
    · obtain ⟨i', rfl⟩ := hi
      have : ∑ l : Option Λ', ggAttachCartan C k (e i') (e l) * y' l =
          ∑ l, ggAttachCartan C' k' i' l * y' l := by
        apply Finset.sum_congr rfl
        intro l _
        rw [key i' l]
      rw [this]
      exact h1 i'
    · push_neg at hi
      apply Finset.sum_nonneg
      intro l _
      exact mul_nonneg_of_nonpos_of_nonpos (hX i l hi) (hy' l)
  · obtain ⟨i₀, hi₀⟩ := h2
    refine ⟨e i₀, ?_⟩
    rw [hsum (e i₀)]
    have : ∑ l : Option Λ', ggAttachCartan C k (e i₀) (e l) * y' l =
        ∑ l, ggAttachCartan C' k' i₀ l * y' l := by
      apply Finset.sum_congr rfl
      intro l _
      rw [key i₀ l]
    rw [this]
    exact hi₀

end Tail

end CFSG.StandardType
