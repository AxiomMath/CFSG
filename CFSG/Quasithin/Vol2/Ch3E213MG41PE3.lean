module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big.IPL

variable {k : Type} [Field k] [CharP k 2]

@[expose] def rotC (c : k) (v : k × k) : k × k :=
  (v.1 * (1 + c ^ 2) + v.2 * c, v.1 * c + v.2)

@[expose] def qC (c : k) (v : k × k) : k :=
  v.1 ^ 2 + v.2 ^ 2 + c * v.1 * v.2

theorem qC_rotC (c : k) (v : k × k) : qC c (rotC c v) = qC c v := by
  have h0 : (2 : k) = 0 := CharTwo.two_eq_zero
  simp only [qC, rotC]
  linear_combination (c ^ 4 * v.1 ^ 2 + 2 * c ^ 3 * v.1 * v.2 + 2 * c ^ 2 * v.1 ^ 2 +
    c ^ 2 * v.2 ^ 2 + 2 * c * v.1 * v.2) * h0

theorem qC_iterate (c : k) (v : k × k) (j : ℕ) : qC c ((rotC c)^[j] v) = qC c v := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, ih, qC_rotC]

theorem eq_zero_of_iterate_eq {c : k} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {v : k × k} {m : ℕ}
    (hm1 : 1 ≤ m) (hm4 : m ≤ 4) (h : (rotC c)^[m] v = v) : v = 0 := by
  have h0 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hc4 : (c + 1) ^ 4 ≠ 0 := pow_ne_zero 4 fun h' => hc1 (by linear_combination h' - h0)
  obtain ⟨t, ht, hx, hy⟩ : ∃ t : k, t ≠ 0 ∧ t * v.1 = 0 ∧ t * v.2 = 0 := by
    interval_cases m
    · have h' : rotC c v = v := h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h'
      simp only [rotC] at h1 h2
      exact ⟨c ^ 2, pow_ne_zero 2 hc0, by linear_combination c * h2,
        by linear_combination c * h1 - c ^ 2 * h2⟩
    · have h' : rotC c (rotC c v) = v := h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h'
      simp only [rotC] at h1 h2
      refine ⟨c ^ 4, pow_ne_zero 4 hc0, ?_, ?_⟩
      · linear_combination (-c ^ 2) * h1 + (c ^ 3 + 2 * c) * h2 + (-2 * c ^ 2 * v.1) * h0
      · linear_combination (c ^ 3 + 2 * c) * h1 + (-c ^ 4 - 3 * c ^ 2) * h2 +
          (-2 * c ^ 2 * v.2) * h0
    · have h' : rotC c (rotC c (rotC c v)) = v := h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h'
      simp only [rotC] at h1 h2
      refine ⟨c ^ 2 * (c + 1) ^ 4, mul_ne_zero (pow_ne_zero 2 hc0) hc4, ?_, ?_⟩
      · linear_combination (-c ^ 4 - 3 * c ^ 2) * h1 + (c ^ 5 + 4 * c ^ 3 + 3 * c) * h2 +
          (2 * c ^ 5 * v.1 + 2 * c ^ 3 * v.1 - 4 * c ^ 2 * v.1) * h0
      · linear_combination (c ^ 5 + 4 * c ^ 3 + 3 * c) * h1 +
          (-c ^ 6 - 5 * c ^ 4 - 6 * c ^ 2) * h2 +
          (2 * c ^ 5 * v.2 + 2 * c ^ 3 * v.2 - 4 * c ^ 2 * v.2) * h0
    · have h' : rotC c (rotC c (rotC c (rotC c v))) = v := h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h'
      simp only [rotC] at h1 h2
      refine ⟨c ^ 8, pow_ne_zero 8 hc0, ?_, ?_⟩
      · linear_combination (-c ^ 6 - 5 * c ^ 4 - 6 * c ^ 2) * h1 +
          (c ^ 7 + 6 * c ^ 5 + 10 * c ^ 3 + 4 * c) * h2 +
          (-4 * c ^ 6 * v.1 - 10 * c ^ 4 * v.1 - 8 * c ^ 2 * v.1) * h0
      · linear_combination (c ^ 7 + 6 * c ^ 5 + 10 * c ^ 3 + 4 * c) * h1 +
          (-c ^ 8 - 7 * c ^ 6 - 15 * c ^ 4 - 10 * c ^ 2) * h2 +
          (-4 * c ^ 6 * v.2 - 10 * c ^ 4 * v.2 - 8 * c ^ 2 * v.2) * h0
  exact Prod.ext ((mul_eq_zero.mp hx).resolve_left ht) ((mul_eq_zero.mp hy).resolve_left ht)

theorem iterate_rotC_inj {c : k} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {v : k × k} (hv : qC c v ≠ 0)
    {i j : ℕ} (hi : i < 5) (hj : j < 5) (h : (rotC c)^[i] v = (rotC c)^[j] v) : i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi h.symm (by omega)).symm
  by_contra hne
  have e : (rotC c)^[j - i] ((rotC c)^[i] v) = (rotC c)^[i] v := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij, h]
  have h0 := eq_zero_of_iterate_eq hc0 hc1 (by omega) (by omega) e
  apply hv
  rw [← qC_iterate c v i, h0]
  simp [qC]

theorem exists_lt_five_not {p q : ℕ → Prop}
    (hp : ∀ i j l, i < 5 → j < 5 → l < 5 → p i → p j → p l → i = j ∨ i = l ∨ j = l)
    (hq : ∀ i j l, i < 5 → j < 5 → l < 5 → q i → q j → q l → i = j ∨ i = l ∨ j = l) :
    ∃ j < 5, ¬p j ∧ ¬q j := by
  classical
  have card_le : ∀ r : ℕ → Prop,
      (∀ i j l, i < 5 → j < 5 → l < 5 → r i → r j → r l → i = j ∨ i = l ∨ j = l) →
        ((Finset.range 5).filter r).card ≤ 2 := by
    intro r hr
    by_contra hlt
    obtain ⟨i, hi, j, hj, l, hl, hij, hil, hjl⟩ := Finset.two_lt_card.mp (not_le.mp hlt)
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj hl
    rcases hr i j l hi.1 hj.1 hl.1 hi.2 hj.2 hl.2 with h | h | h
    · exact hij h
    · exact hil h
    · exact hjl h
  have hlt : ((Finset.range 5).filter p ∪ (Finset.range 5).filter q).card <
      (Finset.range 5).card := by
    calc _ ≤ ((Finset.range 5).filter p).card + ((Finset.range 5).filter q).card :=
          Finset.card_union_le _ _
      _ ≤ 2 + 2 := add_le_add (card_le p hp) (card_le q hq)
      _ < (Finset.range 5).card := by rw [Finset.card_range]; norm_num
  obtain ⟨j, hj, hj'⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_range] at hj
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, not_or, not_and] at hj'
  exact ⟨j, hj, hj'.1 hj, hj'.2 hj⟩

theorem two_good_pairs {p₀ p₁ p₂ p₃ : ℕ → Prop} (h₀ : ∀ i j, i < 5 → j < 5 → p₀ i → p₀ j → i = j)
    (h₁ : ∀ i j l, i < 5 → j < 5 → l < 5 → p₁ i → p₁ j → p₁ l → i = j ∨ i = l ∨ j = l)
    (h₂ : ∀ i j l, i < 5 → j < 5 → l < 5 → p₂ i → p₂ j → p₂ l → i = j ∨ i = l ∨ j = l)
    (h₃ : ∀ i j l, i < 5 → j < 5 → l < 5 → p₃ i → p₃ j → p₃ l → i = j ∨ i = l ∨ j = l)
    (d₀₂ : ∀ j < 5, p₀ j → p₂ j → False) (d₀₃ : ∀ j < 5, p₀ j → p₃ j → False)
    (d₁₂ : ∀ j < 5, p₁ j → p₂ j → False) (d₁₃ : ∀ j < 5, p₁ j → p₃ j → False)
    (d₂₃ : ∀ j < 5, p₂ j → p₃ j → False) :
    ((∃ j < 5, ¬p₀ j ∧ ¬p₁ j ∧ ¬p₂ j) ∧ ∃ j < 5, ¬p₀ j ∧ ¬p₁ j ∧ ¬p₃ j) ∨
      ((∃ j < 5, ¬p₀ j ∧ ¬p₁ j ∧ ¬p₂ j) ∧ ∃ j < 5, ¬p₀ j ∧ ¬p₂ j ∧ ¬p₃ j) ∨
      ((∃ j < 5, ¬p₀ j ∧ ¬p₁ j ∧ ¬p₃ j) ∧ ∃ j < 5, ¬p₀ j ∧ ¬p₂ j ∧ ¬p₃ j) := by
  have h₀' : ∀ i j l, i < 5 → j < 5 → l < 5 → p₀ i → p₀ j → p₀ l → i = j ∨ i = l ∨ j = l :=
    fun i j _ hi hj _ hpi hpj _ => Or.inl (h₀ i j hi hj hpi hpj)
  have E : ∀ p q : ℕ → Prop,
      (∀ i j l, i < 5 → j < 5 → l < 5 → p i → p j → p l → i = j ∨ i = l ∨ j = l) →
        (∀ j < 5, ¬q j) → ∃ j < 5, ¬p₀ j ∧ ¬p j ∧ ¬q j := by
    intro p q hp hq
    obtain ⟨j, hj, h0j, hpj⟩ := exists_lt_five_not h₀' hp
    exact ⟨j, hj, h0j, hpj, hq j hj⟩
  have C : ∀ p q n : ℕ → Prop, (∀ j < 5, p₀ j → n j → False) → (∀ j < 5, p j → n j → False) →
      (∀ j < 5, q j → n j → False) → (∃ j < 5, ¬p₀ j ∧ ¬p j ∧ ¬q j) ∨ ∀ j < 5, ¬n j := by
    intro p q n d0 dp dq
    by_cases hn : ∃ j < 5, n j
    · obtain ⟨j, hj, hnj⟩ := hn
      exact Or.inl ⟨j, hj, fun h => d0 j hj h hnj, fun h => dp j hj h hnj,
        fun h => dq j hj h hnj⟩
    · exact Or.inr fun j hj hnj => hn ⟨j, hj, hnj⟩
  rcases C p₁ p₂ p₃ d₀₃ d₁₃ d₂₃ with g₁₂ | e₃
  · rcases C p₁ p₃ p₂ d₀₂ d₁₂ (fun j hj h3 h2 => d₂₃ j hj h2 h3) with g₁₃ | e₂
    · exact Or.inl ⟨g₁₂, g₁₃⟩
    · obtain ⟨j, hj, a, b, c⟩ := E p₃ p₂ h₃ e₂
      exact Or.inr (Or.inl ⟨g₁₂, j, hj, a, c, b⟩)
  · exact Or.inr (Or.inr ⟨E p₁ p₃ h₁ e₃, E p₂ p₃ h₂ e₃⟩)

end CFSG.Quasithin.Ch3E213M.G41.Big.IPL
