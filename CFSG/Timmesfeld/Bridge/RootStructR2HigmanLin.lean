module

public import CFSG.Timmesfeld.RankOne.SL2

public section

namespace CFSG.Timmesfeld.Bridge.Higman

open Matrix CFSG.Timmesfeld.RankOne
open scoped MatrixGroups

variable {K : Type*} [Field K]

@[expose] def diagElt (t : Kˣ) : SL(2, K) :=
  ⟨!![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

@[expose] def swapElt [CharP K 2] : SL(2, K) :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

theorem upperElt_mulVec (t : K) (v : Fin 2 → K) :
    (upperElt K t : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 0 + t * v 1, v 1] := by
  ext i
  fin_cases i <;> simp [upperElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lowerElt_mulVec (t : K) (v : Fin 2 → K) :
    (lowerElt K t : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 0, t * v 0 + v 1] := by
  ext i
  fin_cases i <;> simp [lowerElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem diagElt_mulVec (t : Kˣ) (v : Fin 2 → K) :
    (diagElt t : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![(t : K) * v 0, ((t⁻¹ : Kˣ) : K) * v 1] := by
  ext i
  fin_cases i <;> simp [diagElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem swapElt_mulVec [CharP K 2] (v : Fin 2 → K) :
    ((swapElt : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 1, v 0] := by
  ext i
  fin_cases i <;> simp [swapElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

omit [Field K] in
theorem eq_vec {R : Type*} (v : Fin 2 → R) : v = ![v 0, v 1] := by
  ext i
  fin_cases i <;> rfl

theorem vec_add (a b c d : K) : (![a, b] : Fin 2 → K) + ![c, d] = ![a + c, b + d] := by
  ext i
  fin_cases i <;> rfl

theorem vec_eq_add (a b : K) : (![a, b] : Fin 2 → K) = ![a, 0] + ![0, b] := by
  rw [vec_add, add_zero, zero_add]

theorem vec_zero : (![0, 0] : Fin 2 → K) = 0 := by
  ext i
  fin_cases i <;> rfl

theorem addSubgroup_eq_top {W : AddSubgroup (Fin 2 → K)}
    (hW : ∀ g : SL(2, K), ∀ v ∈ W, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ W) (hne : W ≠ ⊥) :
    W = ⊤ := by
  have hU : ∀ v ∈ W, ∀ t : K, (![t * v 1, 0] : Fin 2 → K) ∈ W := by
    intro v hv t
    have h1 := W.sub_mem (hW (upperElt K t) v hv) hv
    convert h1 using 1
    rw [upperElt_mulVec]
    ext i
    fin_cases i <;> simp
  have hL : ∀ v ∈ W, ∀ t : K, (![0, t * v 0] : Fin 2 → K) ∈ W := by
    intro v hv t
    have h1 := W.sub_mem (hW (lowerElt K t) v hv) hv
    convert h1 using 1
    rw [lowerElt_mulVec]
    ext i
    fin_cases i <;> simp
  obtain ⟨⟨w, hw⟩, hw0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hne
  have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have he₀ : (![1, 0] : Fin 2 → K) ∈ W := by
    by_cases h1 : w 1 = 0
    · have h0 : w 0 ≠ 0 := by
        intro h0
        apply hw0'
        rw [eq_vec w, h0, h1, vec_zero]
      have he₁ : (![0, 1] : Fin 2 → K) ∈ W := by
        have := hL w hw (w 0)⁻¹
        rwa [inv_mul_cancel₀ h0] at this
      have := hU _ he₁ 1
      simpa using this
    · have := hU w hw (w 1)⁻¹
      rwa [inv_mul_cancel₀ h1] at this
  have he₁ : (![0, 1] : Fin 2 → K) ∈ W := by
    have := hL _ he₀ 1
    simpa using this
  rw [eq_top_iff]
  intro v _
  rw [eq_vec v, vec_eq_add]
  refine W.add_mem ?_ ?_
  · have := hU _ he₁ (v 0)
    simpa using this
  · have := hL _ he₀ (v 1)
    simpa using this

theorem additive_eq_smul [CharP K 2] (f : (Fin 2 → K) → (Fin 2 → K))
    (hadd : ∀ v w, f (v + w) = f v + f w)
    (hf : ∀ (g : SL(2, K)) v,
      f ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ f v) :
    ∃ c : K, ∀ v, f v = c • v := by
  have hf0 : f 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have h1 : ∀ x : K, f ![x, 0] 1 = 0 := by
    intro x
    have h := congrFun (hf (upperElt K 1) ![x, 0]) 0
    rw [upperElt_mulVec, upperElt_mulVec] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero,
      one_mul] at h
    exact left_eq_add.mp h
  have h2 : ∀ x l : K, f ![l * x, 0] = ![l * f ![0, x] 1, 0] := by
    intro x l
    have h := hf (upperElt K l) ![0, x]
    rw [upperElt_mulVec, upperElt_mulVec] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_add] at h
    rw [vec_eq_add, hadd] at h
    have h' : f ![l * x, 0] = ![f ![0, x] 0 + l * f ![0, x] 1, f ![0, x] 1] - f ![0, x] := by
      rw [← h, add_sub_cancel_right]
    rw [h', eq_vec (f ![0, x]), sub_eq_add_neg]
    ext i
    fin_cases i <;> simp
  set c := f ![1, 0] 0 with hc
  have hL : ∀ x : K, f ![x, 0] = ![c * x, 0] := by
    intro x
    have e1 := h2 x 1
    have e2 := h2 1 x
    rw [one_mul, one_mul] at e1
    rw [mul_one] at e2
    rw [e2]
    have : f ![0, 1] 1 = c := by
      have := h2 1 1
      rw [one_mul, one_mul] at this
      rw [hc, this]
      simp
    rw [this, mul_comm]
  have hR : ∀ y : K, f ![0, y] = ![0, c * y] := by
    intro y
    have h := hf swapElt ![y, 0]
    rw [swapElt_mulVec, swapElt_mulVec, hL] at h
    simpa using h
  refine ⟨c, fun v => ?_⟩
  rw [eq_vec v, vec_eq_add, hadd, hL, hR, vec_add]
  ext i
  fin_cases i <;> simp

theorem bilinear_eq_zero [CharP K 2] {t₀ : K} (ht₀ : t₀ ≠ 0) (ht₁ : t₀ ≠ 1)
    (β : (Fin 2 → K) → (Fin 2 → K) → (Fin 2 → K))
    (hadd₁ : ∀ v v' w, β (v + v') w = β v w + β v' w)
    (hadd₂ : ∀ v w w', β v (w + w') = β v w + β v w')
    (hβ : ∀ (g : SL(2, K)) v w, β ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v)
      ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ β v w)
    (v w : Fin 2 → K) : β v w = 0 := by
  have h1 : ∀ x x' : K, β ![x, 0] ![x', 0] 1 = 0 := by
    intro x x'
    have h := congrFun (hβ (upperElt K 1) ![x, 0] ![x', 0]) 0
    rw [upperElt_mulVec, upperElt_mulVec, upperElt_mulVec] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero,
      one_mul] at h
    exact left_eq_add.mp h
  have h2 : ∀ x y l : K, β ![x, 0] ![l * y, 0] = ![l * β ![x, 0] ![0, y] 1, 0] := by
    intro x y l
    have h := hβ (upperElt K l) ![x, 0] ![0, y]
    rw [upperElt_mulVec, upperElt_mulVec, upperElt_mulVec] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero,
      zero_add] at h
    rw [vec_eq_add (l * y) y, hadd₂] at h
    have h' : β ![x, 0] ![l * y, 0] = ![β ![x, 0] ![0, y] 0 + l * β ![x, 0] ![0, y] 1,
        β ![x, 0] ![0, y] 1] - β ![x, 0] ![0, y] := by
      rw [← h, add_sub_cancel_right]
    rw [h', eq_vec (β ![x, 0] ![0, y]), sub_eq_add_neg]
    ext i
    fin_cases i <;> simp
  have h3 : ∀ x y l : K, β ![l * x, 0] ![y, 0] = ![l * β ![0, x] ![y, 0] 1, 0] := by
    intro x y l
    have h := hβ (upperElt K l) ![0, x] ![y, 0]
    rw [upperElt_mulVec, upperElt_mulVec, upperElt_mulVec] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero,
      zero_add] at h
    rw [vec_eq_add (l * x) x, hadd₁] at h
    have h' : β ![l * x, 0] ![y, 0] = ![β ![0, x] ![y, 0] 0 + l * β ![0, x] ![y, 0] 1,
        β ![0, x] ![y, 0] 1] - β ![0, x] ![y, 0] := by
      rw [← h, add_sub_cancel_right]
    rw [h', eq_vec (β ![0, x] ![y, 0]), sub_eq_add_neg]
    ext i
    fin_cases i <;> simp
  set P : K → K → K := fun x y => β ![x, 0] ![y, 0] 0 with hP
  have hP2 : ∀ x y l : K, P x (l * y) = l * P x y := by
    intro x y l
    have e1 := congrFun (h2 x y l) 0
    have e2 := congrFun (h2 x y 1) 0
    simp only [Matrix.cons_val_zero, one_mul] at e1 e2
    simp only [hP]
    rw [e1, e2]
  have hP3 : ∀ x y l : K, P (l * x) y = l * P x y := by
    intro x y l
    have e1 := congrFun (h3 x y l) 0
    have e2 := congrFun (h3 x y 1) 0
    simp only [Matrix.cons_val_zero, one_mul] at e1 e2
    simp only [hP]
    rw [e1, e2]
  have hPxy : ∀ x y : K, P x y = x * y * P 1 1 := by
    intro x y
    have e1 := hP3 1 y x
    have e2 := hP2 1 1 y
    rw [mul_one] at e1 e2
    rw [e1, e2, mul_assoc]
  have hP11 : P 1 1 = 0 := by
    set t : Kˣ := Units.mk0 t₀ ht₀ with htdef
    have h := congrFun (hβ (diagElt t) ![1, 0] ![1, 0]) 0
    simp only [diagElt_mulVec] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
      mul_zero] at h
    have e : P t₀ t₀ = t₀ * P 1 1 := by
      simp only [hP]
      rw [show ((t : K)) = t₀ from rfl] at h
      exact h
    rw [hPxy] at e
    have e' : t₀ * (t₀ - 1) * P 1 1 = 0 := by
      rw [mul_sub, mul_one, sub_mul, e, sub_self]
    rcases mul_eq_zero.mp e' with h0 | h0
    · rcases mul_eq_zero.mp h0 with h0 | h0
      · exact absurd h0 ht₀
      · exact absurd (sub_eq_zero.mp h0) ht₁
    · exact h0
  have hLL : ∀ x y : K, β ![x, 0] ![y, 0] = 0 := by
    intro x y
    rw [eq_vec (β ![x, 0] ![y, 0]), h1, ← vec_zero]
    congr 1
    show P x y = 0
    rw [hPxy, hP11, mul_zero]
  have hRR : ∀ x y : K, β ![0, x] ![0, y] = 0 := by
    intro x y
    have h := hβ swapElt ![x, 0] ![y, 0]
    rw [swapElt_mulVec, swapElt_mulVec, hLL, mulVec_zero] at h
    simpa using h
  have hLR : ∀ x y : K, β ![x, 0] ![0, y] = 0 := by
    intro x y
    have e1 : β ![x, 0] ![0, y] 1 = 0 := by
      have := congrFun (h2 x y 1) 0
      rw [one_mul, hLL] at this
      simpa using this.symm
    have e0 : β ![x, 0] ![0, y] 0 = 0 := by
      have h := congrFun (hβ (lowerElt K 1) ![x, 0] ![0, y]) 1
      rw [lowerElt_mulVec, lowerElt_mulVec, lowerElt_mulVec] at h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero,
        add_zero, one_mul, zero_add] at h
      rw [vec_eq_add x x, hadd₁, hRR, add_zero] at h
      exact (left_eq_add.mp (h.trans (add_comm _ _))).symm ▸ rfl
    rw [eq_vec (β ![x, 0] ![0, y]), e0, e1, vec_zero]
  have hRL : ∀ x y : K, β ![0, x] ![y, 0] = 0 := by
    intro x y
    have h := hβ swapElt ![x, 0] ![0, y]
    rw [swapElt_mulVec, swapElt_mulVec, hLR, mulVec_zero] at h
    simpa using h
  rw [eq_vec v, eq_vec w, vec_eq_add (v 0), vec_eq_add (w 0), hadd₁, hadd₂, hadd₂, hLL, hLR,
    hRL, hRR, add_zero, add_zero]

theorem eq_one_of_map_mul [Fintype K] [CharP K 2] {μ c : K} (hμ : μ ≠ 0) (hc : c ≠ 0)
    (f : K → K) (hf : ∀ u, f (μ * u) = μ * f u + c * (1 + μ) * u) : μ = 1 := by
  have h2 : ∀ u, f (μ ^ 2 * u) = μ ^ 2 * f u := by
    intro u
    rw [pow_two, mul_assoc, hf, hf]
    have : c * (1 + μ) * (μ * u) + μ * (c * (1 + μ) * u) = 0 := by
      rw [show μ * (c * (1 + μ) * u) = c * (1 + μ) * (μ * u) by ring, CharTwo.add_self_eq_zero]
    calc μ * (μ * f u + c * (1 + μ) * u) + c * (1 + μ) * (μ * u)
        = μ * μ * f u + (c * (1 + μ) * (μ * u) + μ * (c * (1 + μ) * u)) := by ring
      _ = μ * μ * f u := by rw [this, add_zero]
  have hpow : ∀ k : ℕ, ∀ u, f (μ ^ (2 * k) * u) = μ ^ (2 * k) * f u := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add, mul_assoc, h2, ih, ← mul_assoc]
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have heven : Fintype.card K % 2 = 0 := FiniteField.even_card_of_char_two hchar
  have hcard : 2 ≤ Fintype.card K := Fintype.one_lt_card
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card K - 1 = 2 * k + 1 := ⟨(Fintype.card K - 2) / 2, by omega⟩
  have hμq : μ ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact FiniteField.pow_card_sub_one_eq_one μ hμ
  have e := hf (μ ^ (2 * k))
  have e1 : μ * μ ^ (2 * k) = 1 := by rw [← pow_succ', hμq]
  have e2 := hpow k 1
  rw [mul_one] at e2
  rw [e1, e2, ← mul_assoc, e1, one_mul, left_eq_add] at e
  have hμk : μ ^ (2 * k) ≠ 0 := pow_ne_zero _ hμ
  have h1μ : 1 + μ = 0 := by
    rcases mul_eq_zero.mp e with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hc
      · exact h
    · exact absurd (by simpa using h) hμk
  have := (add_eq_zero_iff_eq_neg.mp h1μ)
  rw [CharTwo.neg_eq] at this
  exact this.symm

end CFSG.Timmesfeld.Bridge.Higman
