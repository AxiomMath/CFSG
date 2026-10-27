module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType.ZS

variable {K : Type*} [Field K]

private lemma zfs_signs_vec (a b c d : K) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1) :
    ∀ i, (![a, b, c, d] : Fin 4 → K) i = 1 ∨ (![a, b, c, d] : Fin 4 → K) i = -1 := by
  intro i
  fin_cases i <;> simp [ha, hb, hc, hd]

private lemma zfs_signs_p1 :
    ∀ i, (![1, 1, -1, -1] : Fin 4 → K) i = 1 ∨ (![1, 1, -1, -1] : Fin 4 → K) i = -1 :=
  zfs_signs_vec 1 1 (-1) (-1) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)

private lemma zfs_signs_p2 :
    ∀ i, (![1, -1, 1, -1] : Fin 4 → K) i = 1 ∨ (![1, -1, 1, -1] : Fin 4 → K) i = -1 :=
  zfs_signs_vec 1 (-1) 1 (-1) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)

private lemma zfs_signs_p3 :
    ∀ i, (![1, -1, -1, 1] : Fin 4 → K) i = 1 ∨ (![1, -1, -1, 1] : Fin 4 → K) i = -1 :=
  zfs_signs_vec 1 (-1) (-1) 1 (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)

private lemma zfs_mul_signs {ε δ : Fin 4 → K} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hδ : ∀ i, δ i = 1 ∨ δ i = -1) :
    ∀ i, (ε * δ) i = 1 ∨ (ε * δ) i = -1 := by
  intro i
  rcases hε i with h' | h' <;> rcases hδ i with h'' | h'' <;> simp [Pi.mul_apply, h', h'']

private lemma zfs_sign_ne_zero {ε : Fin 4 → K} {i : Fin 4} (h : ε i = 1 ∨ ε i = -1) :
    ε i ≠ 0 := by
  rcases h with h' | h' <;> simp [h']

private lemma zfs_mul_self_eq_one {ε : Fin 4 → K} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∀ i, ε i * ε i = 1 := by
  intro i
  rcases hε i with h' | h' <;> simp [h']

private lemma zfs_prod_shift_eq_zero {z : Fin 4 → K} (hz : ∀ i, z i ≠ 0)
    (hsum : ∑ i, z i = 0) (hsuminv : ∑ i, 1 / z i = 0) :
    (z 0 + z 1) * (z 0 + z 2) * (z 0 + z 3) = 0 := by
  have hs : z 0 + z 1 + z 2 + z 3 = 0 := by simpa [Fin.sum_univ_four] using hsum
  have ht : 1 / z 0 + 1 / z 1 + 1 / z 2 + 1 / z 3 = 0 := by
    simpa [Fin.sum_univ_four] using hsuminv
  field_simp [hz 0, hz 1, hz 2, hz 3] at ht
  have h3 : z 3 = -(z 0 + z 1 + z 2) := by linear_combination hs
  rw [h3] at ht ⊢
  linear_combination ht

private lemma zfs_key (h2 : (2 : K) ≠ 0) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (2 * (a + b) = 0 ∧ 2 * (1 / a + 1 / b) = 0) ∨
      (2 * (a + b)) * (2 * (1 / a + 1 / b)) = 4) :
    a + b = 0 ∨ (a + b) ^ 2 = a * b := by
  rcases h with ⟨hS, -⟩ | hST
  · exact Or.inl ((mul_eq_zero.mp hS).resolve_left h2)
  · right
    have hEq : (2 : K) * 2 * ((a + b) * (a + b)) = (2 : K) * 2 * (a * b) := by
      field_simp [ha, hb] at hST
      linear_combination hST
    simpa [pow_two] using mul_left_cancel₀ (mul_ne_zero h2 h2) hEq

private lemma zfs_key_of {z δ : Fin 4 → K} (hδ : ∀ i, δ i = 1 ∨ δ i = -1)
    (h2 : (2 : K) ≠ 0)
    (hne : ¬ ∃ (c : K) (δ : Fin 4 → K), (∀ i, δ i = 1 ∨ δ i = -1) ∧ z = c • δ)
    {a b f g : K} (ha : a ≠ 0) (hb : b ≠ 0) (hf : f = 2 * (a + b))
    (hg : g = 2 * (1 / a + 1 / b))
    (h : (∃ c : K, z = c • δ) ∨ (f = 0 ∧ g = 0) ∨ f * g = 4) :
    a + b = 0 ∨ (a + b) ^ 2 = a * b := by
  rcases h with ⟨c, hc⟩ | hrest
  · exact absurd ⟨c, δ, hδ, hc⟩ hne
  · rw [hf, hg] at hrest
    exact zfs_key h2 ha hb hrest

private lemma zfs_contra_pair (h2 : (2 : K) ≠ 0) {u v : K} (hu : u ≠ 0) (hv : v ≠ 0)
    (h1 : (u + v) ^ 2 = u * v) (h2' : (u - v) ^ 2 = -(u * v)) : False := by
  have h : (2 : K) * (u * v) = 0 := by linear_combination h1 - h2'
  rcases mul_eq_zero.mp h with h | h
  · exact h2 h
  · exact mul_ne_zero hu hv h

private lemma zfs_mult_of_eqs {z : Fin 4 → K} {d1 d2 d3 : K}
    (h1 : z 1 = d1 * z 0) (h2 : z 2 = d2 * z 0) (h3 : z 3 = d3 * z 0)
    (hd1 : d1 = 1 ∨ d1 = -1) (hd2 : d2 = 1 ∨ d2 = -1) (hd3 : d3 = 1 ∨ d3 = -1) :
    ∃ (c : K) (δ : Fin 4 → K), (∀ i, δ i = 1 ∨ δ i = -1) ∧ z = c • δ := by
  refine ⟨z 0, ![1, d1, d2, d3], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hd1, hd2, hd3]
  · funext i
    fin_cases i <;> simp [h1, h2, h3] <;> ring

private lemma zfs_mult12 {z : Fin 4 → K} (hs : z 0 + z 1 + z 2 + z 3 = 0)
    (h1 : z 0 + z 1 = 0) (h2 : z 0 + z 2 = 0) :
    ∃ (c : K) (δ : Fin 4 → K), (∀ i, δ i = 1 ∨ δ i = -1) ∧ z = c • δ := by
  have e1 : z 1 = (-1 : K) * z 0 := by linear_combination h1
  have e2 : z 2 = (-1 : K) * z 0 := by linear_combination h2
  have e3 : z 3 = (1 : K) * z 0 := by linear_combination hs - h1 - h2
  exact zfs_mult_of_eqs e1 e2 e3 (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)

private lemma zfs_mult13 {z : Fin 4 → K} (hs : z 0 + z 1 + z 2 + z 3 = 0)
    (h1 : z 0 + z 1 = 0) (h3 : z 0 + z 3 = 0) :
    ∃ (c : K) (δ : Fin 4 → K), (∀ i, δ i = 1 ∨ δ i = -1) ∧ z = c • δ := by
  have e1 : z 1 = (-1 : K) * z 0 := by linear_combination h1
  have e3 : z 3 = (-1 : K) * z 0 := by linear_combination h3
  have e2 : z 2 = (1 : K) * z 0 := by linear_combination hs - h1 - h3
  exact zfs_mult_of_eqs e1 e2 e3 (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)

private lemma zfs_mult23 {z : Fin 4 → K} (hs : z 0 + z 1 + z 2 + z 3 = 0)
    (h2 : z 0 + z 2 = 0) (h3 : z 0 + z 3 = 0) :
    ∃ (c : K) (δ : Fin 4 → K), (∀ i, δ i = 1 ∨ δ i = -1) ∧ z = c • δ := by
  have e2 : z 2 = (-1 : K) * z 0 := by linear_combination h2
  have e3 : z 3 = (-1 : K) * z 0 := by linear_combination h3
  have e1 : z 1 = (1 : K) * z 0 := by linear_combination hs - h2 - h3
  exact zfs_mult_of_eqs e1 e2 e3 (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)

private lemma zfs_contra1 (h2 : (2 : K) ≠ 0) {z : Fin 4 → K} (hz : ∀ i, z i ≠ 0)
    (hs : z 0 + z 1 + z 2 + z 3 = 0)
    (k2 : z 0 + z 2 = 0 ∨ (z 0 + z 2) ^ 2 = z 0 * z 2)
    (k3 : z 0 + z 3 = 0 ∨ (z 0 + z 3) ^ 2 = z 0 * z 3)
    (h1 : z 0 + z 1 = 0) (hA2 : z 0 + z 2 ≠ 0) (hA3 : z 0 + z 3 ≠ 0) : False := by
  have hbc : z 2 + z 3 = 0 := by linear_combination hs - h1
  have hq2 : (z 0 + z 2) ^ 2 = z 0 * z 2 := k2.resolve_left hA2
  have hq3 : (z 0 + z 3) ^ 2 = z 0 * z 3 := k3.resolve_left hA3
  have hz3 : z 3 = -z 2 := by linear_combination hbc
  refine zfs_contra_pair h2 (hz 0) (hz 2) hq2 ?_
  rw [hz3] at hq3
  linear_combination hq3

private lemma zfs_contra2 (h2 : (2 : K) ≠ 0) {z : Fin 4 → K} (hz : ∀ i, z i ≠ 0)
    (hs : z 0 + z 1 + z 2 + z 3 = 0)
    (k1 : z 0 + z 1 = 0 ∨ (z 0 + z 1) ^ 2 = z 0 * z 1)
    (k3 : z 0 + z 3 = 0 ∨ (z 0 + z 3) ^ 2 = z 0 * z 3)
    (h2' : z 0 + z 2 = 0) (hA1 : z 0 + z 1 ≠ 0) (hA3 : z 0 + z 3 ≠ 0) : False := by
  have hbc : z 1 + z 3 = 0 := by linear_combination hs - h2'
  have hq1 : (z 0 + z 1) ^ 2 = z 0 * z 1 := k1.resolve_left hA1
  have hq3 : (z 0 + z 3) ^ 2 = z 0 * z 3 := k3.resolve_left hA3
  have hz3 : z 3 = -z 1 := by linear_combination hbc
  refine zfs_contra_pair h2 (hz 0) (hz 1) hq1 ?_
  rw [hz3] at hq3
  linear_combination hq3

private lemma zfs_contra3 (h2 : (2 : K) ≠ 0) {z : Fin 4 → K} (hz : ∀ i, z i ≠ 0)
    (hs : z 0 + z 1 + z 2 + z 3 = 0)
    (k1 : z 0 + z 1 = 0 ∨ (z 0 + z 1) ^ 2 = z 0 * z 1)
    (k2 : z 0 + z 2 = 0 ∨ (z 0 + z 2) ^ 2 = z 0 * z 2)
    (h3 : z 0 + z 3 = 0) (hA1 : z 0 + z 1 ≠ 0) (hA2 : z 0 + z 2 ≠ 0) : False := by
  have hbc : z 1 + z 2 = 0 := by linear_combination hs - h3
  have hq1 : (z 0 + z 1) ^ 2 = z 0 * z 1 := k1.resolve_left hA1
  have hq2 : (z 0 + z 2) ^ 2 = z 0 * z 2 := k2.resolve_left hA2
  have hz2 : z 2 = -z 1 := by linear_combination hbc
  refine zfs_contra_pair h2 (hz 0) (hz 1) hq1 ?_
  rw [hz2] at hq2
  linear_combination hq2

private lemma zfs_false_of_zero_pairing (h2 : (2 : K) ≠ 0) {z : Fin 4 → K}
    (hz : ∀ i, z i ≠ 0) (hsum : ∑ i, z i = 0) (hsuminv : ∑ i, 1 / z i = 0)
    (hne : ¬ ∃ (c : K) (δ : Fin 4 → K), (∀ i, δ i = 1 ∨ δ i = -1) ∧ z = c • δ)
    (h : ∀ δ : Fin 4 → K, (∀ i, δ i = 1 ∨ δ i = -1) →
      (∃ c : K, z = c • δ) ∨
      ((∑ i, δ i * z i) = 0 ∧ (∑ i, δ i / z i) = 0) ∨
      (∑ i, δ i * z i) * (∑ i, δ i / z i) = 4) : False := by
  have hs : z 0 + z 1 + z 2 + z 3 = 0 := by simpa [Fin.sum_univ_four] using hsum
  have ht : 1 / z 0 + 1 / z 1 + 1 / z 2 + 1 / z 3 = 0 := by
    simpa [Fin.sum_univ_four] using hsuminv
  have hfac := zfs_prod_shift_eq_zero hz hsum hsuminv
  have key1 : z 0 + z 1 = 0 ∨ (z 0 + z 1) ^ 2 = z 0 * z 1 := by
    have hf : (∑ i, (![1, 1, -1, -1] : Fin 4 → K) i * z i) = 2 * (z 0 + z 1) := by
      rw [Fin.sum_univ_four]
      simp
      linear_combination -hs
    have hg : (∑ i, (![1, 1, -1, -1] : Fin 4 → K) i / z i) = 2 * (1 / z 0 + 1 / z 1) := by
      rw [Fin.sum_univ_four]
      simp
      linear_combination -ht
    exact zfs_key_of zfs_signs_p1 h2 hne (hz 0) (hz 1) hf hg (h _ zfs_signs_p1)
  have key2 : z 0 + z 2 = 0 ∨ (z 0 + z 2) ^ 2 = z 0 * z 2 := by
    have hf : (∑ i, (![1, -1, 1, -1] : Fin 4 → K) i * z i) = 2 * (z 0 + z 2) := by
      rw [Fin.sum_univ_four]
      simp
      linear_combination -hs
    have hg : (∑ i, (![1, -1, 1, -1] : Fin 4 → K) i / z i) = 2 * (1 / z 0 + 1 / z 2) := by
      rw [Fin.sum_univ_four]
      simp
      linear_combination -ht
    exact zfs_key_of zfs_signs_p2 h2 hne (hz 0) (hz 2) hf hg (h _ zfs_signs_p2)
  have key3 : z 0 + z 3 = 0 ∨ (z 0 + z 3) ^ 2 = z 0 * z 3 := by
    have hf : (∑ i, (![1, -1, -1, 1] : Fin 4 → K) i * z i) = 2 * (z 0 + z 3) := by
      rw [Fin.sum_univ_four]
      simp
      linear_combination -hs
    have hg : (∑ i, (![1, -1, -1, 1] : Fin 4 → K) i / z i) = 2 * (1 / z 0 + 1 / z 3) := by
      rw [Fin.sum_univ_four]
      simp
      linear_combination -ht
    exact zfs_key_of zfs_signs_p3 h2 hne (hz 0) (hz 3) hf hg (h _ zfs_signs_p3)
  rcases mul_eq_zero.mp hfac with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2'
    · by_cases hA2 : z 0 + z 2 = 0
      · exact absurd (zfs_mult12 hs h1 hA2) hne
      · by_cases hA3 : z 0 + z 3 = 0
        · exact absurd (zfs_mult13 hs h1 hA3) hne
        · exact zfs_contra1 h2 hz hs key2 key3 h1 hA2 hA3
    · by_cases hA1 : z 0 + z 1 = 0
      · exact absurd (zfs_mult12 hs hA1 h2') hne
      · by_cases hA3 : z 0 + z 3 = 0
        · exact absurd (zfs_mult23 hs h2' hA3) hne
        · exact zfs_contra2 h2 hz hs key1 key3 h2' hA1 hA3
  · by_cases hA1 : z 0 + z 1 = 0
    · by_cases hA2 : z 0 + z 2 = 0
      · exact absurd (zfs_mult12 hs hA1 hA2) hne
      · exact absurd (zfs_mult13 hs hA1 h3) hne
    · by_cases hA2 : z 0 + z 2 = 0
      · exact absurd (zfs_mult23 hs hA2 h3) hne
      · exact zfs_contra3 h2 hz hs key1 key2 h3 hA1 hA2

private lemma zfs_expand {x : Fin 4 → K} (hx : ∀ i, x i ≠ 0)
    {e : Fin 4 → K} (he : ∀ i, e i = 1 ∨ e i = -1) :
    (∑ i, e i * x i) * (∑ i, e i / x i) - 4
      = e 0 * e 1 * (x 0 / x 1 + x 1 / x 0) + e 0 * e 2 * (x 0 / x 2 + x 2 / x 0)
        + e 0 * e 3 * (x 0 / x 3 + x 3 / x 0) + e 1 * e 2 * (x 1 / x 2 + x 2 / x 1)
        + e 1 * e 3 * (x 1 / x 3 + x 3 / x 1) + e 2 * e 3 * (x 2 / x 3 + x 3 / x 2) := by
  have h0 : x 0 ≠ 0 := hx 0
  have h1 : x 1 ≠ 0 := hx 1
  have h2 : x 2 ≠ 0 := hx 2
  have h3 : x 3 ≠ 0 := hx 3
  rcases he 0 with e0 | e0 <;> rcases he 1 with e1 | e1 <;>
    rcases he 2 with e2 | e2 <;> rcases he 3 with e3 | e3 <;>
    · simp only [Fin.sum_univ_four, e0, e1, e2, e3]
      field_simp [h0, h1, h2, h3]
      ring

private lemma zfs_Q_eq_zero {x : Fin 4 → K} (hx : ∀ i, x i ≠ 0)
    {e : Fin 4 → K} (he : ∀ i, e i = 1 ∨ e i = -1)
    (h : (∑ i, e i * x i) * (∑ i, e i / x i) = 4) :
    e 0 * e 1 * (x 0 / x 1 + x 1 / x 0) + e 0 * e 2 * (x 0 / x 2 + x 2 / x 0)
      + e 0 * e 3 * (x 0 / x 3 + x 3 / x 0) + e 1 * e 2 * (x 1 / x 2 + x 2 / x 1)
      + e 1 * e 3 * (x 1 / x 3 + x 3 / x 1) + e 2 * e 3 * (x 2 / x 3 + x 3 / x 2) = 0 := by
  rw [← zfs_expand hx he, h]
  ring

private lemma zfs_eq_zero_of_two_mul (h2 : (2 : K) ≠ 0) {w : K}
    (h : (2 : K) * 2 * w = 0) : w = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (mul_ne_zero h2 h2)
  · exact h

private lemma zfs_sq_add_sq_of_ratio {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a / b + b / a = 0) : a ^ 2 + b ^ 2 = 0 := by
  have h' := h
  field_simp [ha, hb] at h'
  linear_combination h'

private lemma zfs_Q_pattern {x : Fin 4 → K} (hx : ∀ i, x i ≠ 0)
    (hO : ∀ e : Fin 4 → K, (∀ i, e i = 1 ∨ e i = -1) →
      (∑ i, e i * x i) * (∑ i, e i / x i) = 4)
    (a b c : K) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1) :
    a * b * (x 0 / x 1 + x 1 / x 0) + a * c * (x 0 / x 2 + x 2 / x 0)
      + a * (x 0 / x 3 + x 3 / x 0) + b * c * (x 1 / x 2 + x 2 / x 1)
      + b * (x 1 / x 3 + x 3 / x 1) + c * (x 2 / x 3 + x 3 / x 2) = 0 := by
  have he := zfs_signs_vec a b c 1 ha hb hc (Or.inl rfl)
  have h := zfs_Q_eq_zero hx he (hO ![a, b, c, 1] he)
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, one_mul, mul_one,
    one_div] using h

private lemma zfs_false_of_all_odd (h2 : (2 : K) ≠ 0) {x : Fin 4 → K} (hx : ∀ i, x i ≠ 0)
    (hO : ∀ e : Fin 4 → K, (∀ i, e i = 1 ∨ e i = -1) →
      (∑ i, e i * x i) * (∑ i, e i / x i) = 4) : False := by
  have q111 := zfs_Q_pattern hx hO 1 1 1 (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  have qm111 := zfs_Q_pattern hx hO (-1) 1 1 (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  have q1m11 := zfs_Q_pattern hx hO 1 (-1) 1 (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  have qm1m11 := zfs_Q_pattern hx hO (-1) (-1) 1 (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  have q11m1 := zfs_Q_pattern hx hO 1 1 (-1) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  have qm11m1 := zfs_Q_pattern hx hO (-1) 1 (-1) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  have q1m1m1 := zfs_Q_pattern hx hO 1 (-1) (-1) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  have e01 : (2 : K) * 2 * (x 0 / x 1 + x 1 / x 0) = 0 := by
    linear_combination q111 - qm111 - q1m11 + qm1m11
  have e02 : (2 : K) * 2 * (x 0 / x 2 + x 2 / x 0) = 0 := by
    linear_combination q111 - qm111 - q11m1 + qm11m1
  have e12 : (2 : K) * 2 * (x 1 / x 2 + x 2 / x 1) = 0 := by
    linear_combination q111 - q1m11 - q11m1 + q1m1m1
  have w01 : x 0 / x 1 + x 1 / x 0 = 0 := zfs_eq_zero_of_two_mul h2 e01
  have w02 : x 0 / x 2 + x 2 / x 0 = 0 := zfs_eq_zero_of_two_mul h2 e02
  have w12 : x 1 / x 2 + x 2 / x 1 = 0 := zfs_eq_zero_of_two_mul h2 e12
  have s01 : x 0 ^ 2 + x 1 ^ 2 = 0 := zfs_sq_add_sq_of_ratio (hx 0) (hx 1) w01
  have s02 : x 0 ^ 2 + x 2 ^ 2 = 0 := zfs_sq_add_sq_of_ratio (hx 0) (hx 2) w02
  have s12 : x 1 ^ 2 + x 2 ^ 2 = 0 := zfs_sq_add_sq_of_ratio (hx 1) (hx 2) w12
  have h2x : (2 : K) * x 0 ^ 2 = 0 := by linear_combination s01 + s02 - s12
  have hx0sq : x 0 ^ 2 = 0 := by
    rcases mul_eq_zero.mp h2x with h | h
    · exact absurd h h2
    · exact h
  have hx0 : x 0 = 0 := by
    have h : x 0 * x 0 = 0 := by rwa [sq] at hx0sq
    exact mul_self_eq_zero.mp h
  exact hx 0 hx0

private lemma zfs_blanket_of_scaled {x z ε : Fin 4 → K} (hzdef : ∀ i, z i = ε i * x i)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hx : ∀ i, x i ≠ 0)
    (h : ∀ e : Fin 4 → K, (∀ i, e i = 1 ∨ e i = -1) →
      (∃ c : K, x = c • e) ∨
      ((∑ i, e i * x i) = 0 ∧ (∑ i, e i / x i) = 0) ∨
      (∑ i, e i * x i) * (∑ i, e i / x i) = 4) :
    ∀ δ : Fin 4 → K, (∀ i, δ i = 1 ∨ δ i = -1) →
      (∃ c : K, z = c • δ) ∨
      ((∑ i, δ i * z i) = 0 ∧ (∑ i, δ i / z i) = 0) ∨
      (∑ i, δ i * z i) * (∑ i, δ i / z i) = 4 := by
  have hεi : ∀ i, ε i * ε i = 1 := zfs_mul_self_eq_one hε
  intro δ hδ
  have hεδ : ∀ i, (ε * δ) i = 1 ∨ (ε * δ) i = -1 := zfs_mul_signs hε hδ
  have hS : (∑ i, (ε * δ) i * x i) = ∑ i, δ i * z i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.mul_apply]
    rw [hzdef i]
    ring
  have hT : (∑ i, (ε * δ) i / x i) = ∑ i, δ i / z i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.mul_apply]
    rw [hzdef i]
    have hxi : x i ≠ 0 := hx i
    have hεne : ε i ≠ 0 := zfs_sign_ne_zero (hε i)
    have hne : ε i * x i ≠ 0 := mul_ne_zero hεne hxi
    field_simp
    linear_combination (δ i) * hεi i
  rcases h (ε * δ) hεδ with ⟨c, hc⟩ | hZO
  · refine Or.inl ⟨c, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    have hxi : x i = c * (ε i * δ i) := by
      have h' := congrFun hc i
      simpa [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using h'
    rw [hzdef i, hxi]
    linear_combination (c * δ i) * hεi i
  · rcases hZO with ⟨h1, h2'⟩ | h3'
    · refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · rw [← hS]
        exact h1
      · rw [← hT]
        exact h2'
    · refine Or.inr (Or.inr ?_)
      rw [← hS, ← hT]
      exact h3'

private lemma zfs_not_mult_scale {x z ε : Fin 4 → K} (hzdef : ∀ i, z i = ε i * x i)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hne : ¬ ∃ (c : K) (δ : Fin 4 → K), (∀ i, δ i = 1 ∨ δ i = -1) ∧ x = c • δ) :
    ¬ ∃ (c : K) (δ : Fin 4 → K), (∀ i, δ i = 1 ∨ δ i = -1) ∧ z = c • δ := by
  rintro ⟨c, δ, hδ, hc⟩
  refine hne ⟨c, ε * δ, ?_, ?_⟩
  · exact zfs_mul_signs hε hδ
  · funext i
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    have hzi : z i = c * δ i := by
      have h' := congrFun hc i
      simpa [Pi.smul_apply, smul_eq_mul] using h'
    have hεi : ε i * ε i = 1 := zfs_mul_self_eq_one hε i
    calc x i = ε i * z i := by rw [hzdef i, ← mul_assoc, hεi, one_mul]
      _ = ε i * (c * δ i) := by rw [hzi]
      _ = c * (ε i * δ i) := by ring

private lemma zfs_sum_inv_scale {x z ε : Fin 4 → K} (hzdef : ∀ i, z i = ε i * x i)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hx : ∀ i, x i ≠ 0)
    (hT : (∑ i, ε i / x i) = 0) : ∑ i, 1 / z i = 0 := by
  have hεi : ∀ i, ε i * ε i = 1 := zfs_mul_self_eq_one hε
  have hpt : ∀ i, 1 / z i = ε i / x i := by
    intro i
    have hxi : x i ≠ 0 := hx i
    have hεne : ε i ≠ 0 := zfs_sign_ne_zero (hε i)
    have hne : ε i * x i ≠ 0 := mul_ne_zero hεne hxi
    rw [hzdef i]
    field_simp
    linear_combination -hεi i
  calc ∑ i, 1 / z i = ∑ i, ε i / x i := Finset.sum_congr rfl (fun i _ => hpt i)
    _ = 0 := hT

theorem exists_eq_smul_sign_of_pairings (h2 : (2 : K) ≠ 0)
    {x : Fin 4 → K} (hx : ∀ i, x i ≠ 0)
    (h : ∀ ε : Fin 4 → K, (∀ i, ε i = 1 ∨ ε i = -1) →
      (∃ c : K, x = c • ε) ∨ ((∑ i, ε i * x i) = 0 ∧ (∑ i, ε i / x i) = 0) ∨
        (∑ i, ε i * x i) * (∑ i, ε i / x i) = 4) :
    ∃ (c : K) (ε : Fin 4 → K), (∀ i, ε i = 1 ∨ ε i = -1) ∧ x = c • ε := by
  by_cases hcon : ∃ (c : K) (ε : Fin 4 → K), (∀ i, ε i = 1 ∨ ε i = -1) ∧ x = c • ε
  · exact hcon
  · by_cases hZ : ∃ ε : Fin 4 → K, (∀ i, ε i = 1 ∨ ε i = -1) ∧
        (∑ i, ε i * x i) = 0 ∧ (∑ i, ε i / x i) = 0
    · obtain ⟨ε, hε, hS, hT⟩ := hZ
      let z : Fin 4 → K := fun i => ε i * x i
      have hzdef : ∀ i, z i = ε i * x i := fun _ => rfl
      have hz : ∀ i, z i ≠ 0 := by
        intro i
        rw [hzdef i]
        exact mul_ne_zero (zfs_sign_ne_zero (hε i)) (hx i)
      have hne := zfs_not_mult_scale hzdef hε hcon
      have hsuminv := zfs_sum_inv_scale hzdef hε hx hT
      have hblanket := zfs_blanket_of_scaled hzdef hε hx h
      exact (zfs_false_of_zero_pairing h2 hz hS hsuminv hne hblanket).elim
    · have hO : ∀ ε : Fin 4 → K, (∀ i, ε i = 1 ∨ ε i = -1) →
          (∑ i, ε i * x i) * (∑ i, ε i / x i) = 4 := by
        intro ε hε
        rcases h ε hε with ⟨c, hc⟩ | hZO
        · exact absurd ⟨c, ε, hε, hc⟩ hcon
        · rcases hZO with ⟨h1, h2'⟩ | h3'
          · exact absurd ⟨ε, hε, h1, h2'⟩ hZ
          · exact h3'
      exact (zfs_false_of_all_odd h2 hx hO).elim

end CFSG.StandardType.ZS
