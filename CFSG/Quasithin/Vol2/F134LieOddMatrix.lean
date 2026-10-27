module

public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.Quasithin.F134.LieOdd

open Matrix

variable {K : Type} [Field K]

theorem offDiag_eq_zero_of_commute_diagonal {A : Matrix (Fin 3) (Fin 3) K} {δ : Fin 3 → K}
    (h : A * diagonal δ = diagonal δ * A) {i j : Fin 3} (hij : δ i ≠ δ j) : A i j = 0 := by
  have h' := congrFun (congrFun h i) j
  rw [mul_diagonal, diagonal_mul] at h'
  have : A i j * (δ j - δ i) = 0 := by rw [mul_sub, h']; ring
  rcases mul_eq_zero.1 this with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.1 h0).symm hij

@[expose] def IsDiag3 (A : Matrix (Fin 3) (Fin 3) K) : Prop := ∀ i j, i ≠ j → A i j = 0

theorem IsDiag3.eq_diagonal {A : Matrix (Fin 3) (Fin 3) K} (h : IsDiag3 A) :
    A = diagonal fun i => A i i := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [h i j hij, diagonal_apply_ne _ hij]

theorem IsDiag3.commute {A B : Matrix (Fin 3) (Fin 3) K} (hA : IsDiag3 A) (hB : IsDiag3 B) :
    A * B = B * A := by
  rw [hA.eq_diagonal, hB.eq_diagonal, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  ring

theorem isDiag3_of_commute_diagonal {A : Matrix (Fin 3) (Fin 3) K} {δ : Fin 3 → K}
    (hδ : Function.Injective δ) (h : A * diagonal δ = diagonal δ * A) : IsDiag3 A :=
  fun _ _ hij => offDiag_eq_zero_of_commute_diagonal h (hδ.ne hij)

@[expose] def IsRegular (y : Matrix (Fin 3) (Fin 3) K) : Prop :=
  ∃ C C' : Matrix (Fin 3) (Fin 3) K, C * C' = 1 ∧ C' * C = 1 ∧ ∃ δ : Fin 3 → K,
    Function.Injective δ ∧ C' * y * C = diagonal δ

theorem isDiag3_conj_of_commute {y : Matrix (Fin 3) (Fin 3) K} {C C' : Matrix (Fin 3) (Fin 3) K}
    (hCC' : C * C' = 1) {δ : Fin 3 → K} (hδ : Function.Injective δ)
    (hy : C' * y * C = diagonal δ) {g : Matrix (Fin 3) (Fin 3) K} (hg : g * y = y * g) :
    IsDiag3 (C' * g * C) := by
  refine isDiag3_of_commute_diagonal hδ ?_
  rw [← hy]
  calc C' * g * C * (C' * y * C) = C' * (g * (C * C') * y) * C := by simp only [Matrix.mul_assoc]
    _ = C' * (y * (C * C') * g) * C := by rw [hCC', Matrix.mul_one, Matrix.mul_one, hg]
    _ = C' * y * C * (C' * g * C) := by simp only [Matrix.mul_assoc]

theorem commute_of_conj {C C' A B : Matrix (Fin 3) (Fin 3) K} (hCC' : C * C' = 1)
    (h : C' * A * C * (C' * B * C) = C' * B * C * (C' * A * C)) :
    A * B = B * A := by
  have h' : C * (C' * A * C * (C' * B * C)) * C' = C * (C' * B * C * (C' * A * C)) * C' := by
    rw [h]
  have e : ∀ X Y : Matrix (Fin 3) (Fin 3) K, C * (C' * X * C * (C' * Y * C)) * C' = X * Y := by
    intro X Y
    calc C * (C' * X * C * (C' * Y * C)) * C' = (C * C') * X * (C * C') * Y * (C * C') := by
          simp only [Matrix.mul_assoc]
      _ = X * Y := by rw [hCC', Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]
  rwa [e, e] at h'

theorem IsRegular.commute_of_commute {y : Matrix (Fin 3) (Fin 3) K} (hy : IsRegular y)
    {g g' : Matrix (Fin 3) (Fin 3) K} (hg : g * y = y * g) (hg' : g' * y = y * g') :
    g * g' = g' * g := by
  obtain ⟨C, C', hCC', -, δ, hδ, hyδ⟩ := hy
  exact commute_of_conj hCC'
    ((isDiag3_conj_of_commute hCC' hδ hyδ hg).commute (isDiag3_conj_of_commute hCC' hδ hyδ hg'))

theorem isRegular_diagonal {δ : Fin 3 → K} (hδ : Function.Injective δ) :
    IsRegular (diagonal δ) :=
  ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, δ, hδ, by rw [Matrix.one_mul, Matrix.mul_one]⟩

theorem isRegular_of_mul_eq {y C : Matrix (Fin 3) (Fin 3) K} (hC : C.det ≠ 0) {δ : Fin 3 → K}
    (hδ : Function.Injective δ) (h : y * C = C * diagonal δ) : IsRegular y := by
  have hu : IsUnit C.det := isUnit_iff_ne_zero.2 hC
  refine ⟨C, C⁻¹, Matrix.mul_nonsing_inv C hu, Matrix.nonsing_inv_mul C hu, δ, hδ, ?_⟩
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul C hu, Matrix.one_mul]

theorem injective_one_omega {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0) :
    Function.Injective ![1, ω, ω ^ 2] := by
  have hω1 : ω ≠ 1 := by
    rintro rfl
    apply h3
    linear_combination hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    apply h3
    linear_combination (2 - ω) * hω + (ω - 1) * h
  have hωω : ω ≠ ω ^ 2 := by
    intro h
    apply hω1
    have : ω * (ω - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hω0
    · exact sub_eq_zero.1 h'
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem isRegular_diag_mul_cyc {d₀ d₁ d₂ ω : K} (hd : d₀ * d₁ * d₂ = 1)
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0) :
    IsRegular (diagonal ![d₀, d₁, d₂] * CFSG.SectionRank.OddCover.cycMat) := by
  have hd₁ : d₁ ≠ 0 := by rintro rfl; simp at hd
  have hd₂ : d₂ ≠ 0 := by rintro rfl; simp at hd
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω
  have hω1 : ω - 1 ≠ 0 := by
    intro h
    apply h3
    linear_combination hω - (ω + 2) * h
  refine isRegular_of_mul_eq (C := !![1, 1, 1; d₁, d₁ * ω ^ 2, d₁ * ω;
    d₁ * d₂, d₁ * d₂ * ω, d₁ * d₂ * ω ^ 2]) ?_ (injective_one_omega hω h3) ?_
  · rw [det_fin_three]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, head_cons, tail_cons, head_fin_const]
    have : d₁ * (d₁ * d₂) * (ω * (ω - 1) * (-3)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hd₁ (mul_ne_zero hd₁ hd₂)) (mul_ne_zero (mul_ne_zero hω0 hω1)
        (neg_ne_zero.2 h3))
    convert this using 1
    linear_combination (d₁ ^ 2 * d₂ * ω * (ω - 1)) * hω
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, CFSG.SectionRank.OddCover.cycMat] <;>
      first
        | ring1
        | linear_combination hd
        | linear_combination ω * hd
        | linear_combination ω ^ 2 * hd
        | linear_combination (-d₁ * (ω - 1)) * hω
        | linear_combination (d₁ * (ω - 1)) * hω
        | linear_combination (-d₁ * d₂ * ω * (ω - 1)) * hω

theorem isRegular_diag_mul_cyc_sq {d₀ d₁ d₂ ω : K} (hd : d₀ * d₁ * d₂ = 1)
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0) :
    IsRegular (diagonal ![d₀, d₁, d₂] * CFSG.SectionRank.OddCover.cycMat ^ 2) := by
  have hd₁ : d₁ ≠ 0 := by rintro rfl; simp at hd
  have hd₂ : d₂ ≠ 0 := by rintro rfl; simp at hd
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω
  have hω1 : ω - 1 ≠ 0 := by
    intro h
    apply h3
    linear_combination hω - (ω + 2) * h
  refine isRegular_of_mul_eq (C := !![1, 1, 1; d₁ * d₂, d₁ * d₂ * ω, d₁ * d₂ * ω ^ 2;
    d₂, d₂ * ω ^ 2, d₂ * ω]) ?_ (injective_one_omega hω h3) ?_
  · rw [det_fin_three]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, head_cons, tail_cons, head_fin_const]
    have : d₁ * d₂ * d₂ * (ω * (1 - ω) * (-3)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hd₁ hd₂) hd₂) (mul_ne_zero (mul_ne_zero hω0
        (by rw [← neg_sub]; exact neg_ne_zero.2 hω1)) (neg_ne_zero.2 h3))
    convert this using 1
    linear_combination (-d₁ * d₂ ^ 2 * ω * (ω - 1)) * hω
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, CFSG.SectionRank.OddCover.cycMat, sq] <;>
      first
        | ring1
        | linear_combination hd
        | linear_combination ω * hd
        | linear_combination ω ^ 2 * hd
        | linear_combination (-d₂ * (ω - 1)) * hω
        | linear_combination (d₂ * (ω - 1)) * hω
        | linear_combination (-d₁ * d₂ * ω * (ω - 1)) * hω

theorem eq_neg_one_of_mul_self {x : K} (h : x * x = 1) (h1 : x ≠ 1) : x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd (sub_eq_zero.1 h') h1
  · exact eq_neg_of_add_eq_zero_left h'

theorem diag_involution_cases (h2 : (2 : K) ≠ 0) {a : Fin 3 → K} (ha : ∀ i, a i * a i = 1)
    (had : a 0 * a 1 * a 2 = 1) (ha1 : ¬ ∀ i, a i = 1) :
    a = ![1, -1, -1] ∨ a = ![-1, 1, -1] ∨ a = ![-1, -1, 1] := by
  have h01 : ∀ i, a i = 1 ∨ a i = -1 := fun i => by
    by_cases h : a i = 1
    · exact Or.inl h
    · exact Or.inr (eq_neg_one_of_mul_self (ha i) h)
  have hne : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  have hfun : ∀ x y z : K, a 0 = x → a 1 = y → a 2 = z → a = ![x, y, z] := by
    intro x y z hx hy hz
    funext i
    fin_cases i <;> simp [hx, hy, hz]
  rcases h01 0 with h0 | h0 <;> rcases h01 1 with h1 | h1 <;> rcases h01 2 with h2' | h2'
  · exact absurd (fun i => by fin_cases i <;> assumption) ha1
  · rw [h0, h1, h2'] at had
    exact absurd (by linear_combination had) hne
  · rw [h0, h1, h2'] at had
    exact absurd (by linear_combination had) hne
  · exact Or.inl (hfun _ _ _ h0 h1 h2')
  · rw [h0, h1, h2'] at had
    exact absurd (by linear_combination had) hne
  · exact Or.inr (Or.inl (hfun _ _ _ h0 h1 h2'))
  · exact Or.inr (Or.inr (hfun _ _ _ h0 h1 h2'))
  · rw [h0, h1, h2'] at had
    exact absurd (by linear_combination had) hne

theorem separate_of_involutions (h2 : (2 : K) ≠ 0) {a b : Fin 3 → K}
    (ha : ∀ i, a i * a i = 1) (hb : ∀ i, b i * b i = 1) (had : a 0 * a 1 * a 2 = 1)
    (hbd : b 0 * b 1 * b 2 = 1) (ha1 : ¬ ∀ i, a i = 1) (hb1 : ¬ ∀ i, b i = 1) (hab : a ≠ b)
    {i j : Fin 3} (hij : i ≠ j) : a i ≠ a j ∨ b i ≠ b j := by
  have hne : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  have hne' : (1 : K) ≠ -1 := fun h => hne h.symm
  rcases diag_involution_cases h2 ha had ha1 with rfl | rfl | rfl <;>
    rcases diag_involution_cases h2 hb hbd hb1 with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hab
      | fin_cases i <;> fin_cases j <;> simp_all

theorem conj_mul_conj {C C' A B : Matrix (Fin 3) (Fin 3) K} (hCC' : C * C' = 1) :
    C' * A * C * (C' * B * C) = C' * (A * B) * C := by
  calc C' * A * C * (C' * B * C) = C' * A * (C * C') * B * C := by simp only [Matrix.mul_assoc]
    _ = C' * (A * B) * C := by rw [hCC', Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem IsRegular.commute_of_involutions (h2 : (2 : K) ≠ 0) {y v₁ v₂ : Matrix (Fin 3) (Fin 3) K}
    (hy : IsRegular y) (hv₁ : v₁ * v₁ = 1) (hv₂ : v₂ * v₂ = 1) (hd₁ : v₁.det = 1)
    (hd₂ : v₂.det = 1) (h₁ : v₁ ≠ 1) (h₂ : v₂ ≠ 1) (h₁₂ : v₁ ≠ v₂) (hy₁ : v₁ * y = y * v₁)
    (hy₂ : v₂ * y = y * v₂) {g : Matrix (Fin 3) (Fin 3) K} (hg₁ : g * v₁ = v₁ * g)
    (hg₂ : g * v₂ = v₂ * g) : g * y = y * g := by
  obtain ⟨C, C', hCC', hC'C, δ, hδ, hyδ⟩ := hy
  have hD₁ := isDiag3_conj_of_commute hCC' hδ hyδ hy₁
  have hD₂ := isDiag3_conj_of_commute hCC' hδ hyδ hy₂
  set a : Fin 3 → K := fun i => (C' * v₁ * C) i i
  set b : Fin 3 → K := fun i => (C' * v₂ * C) i i
  have hea : C' * v₁ * C = diagonal a := hD₁.eq_diagonal
  have heb : C' * v₂ * C = diagonal b := hD₂.eq_diagonal
  have hsq : ∀ v : Matrix (Fin 3) (Fin 3) K, v * v = 1 → C' * v * C * (C' * v * C) = 1 := by
    intro v hv
    rw [conj_mul_conj hCC', hv, Matrix.mul_one, hC'C]
  have hdet : ∀ v : Matrix (Fin 3) (Fin 3) K, v.det = 1 → (C' * v * C).det = 1 := by
    intro v hv
    rw [det_mul, det_mul, hv, mul_one, ← det_mul, hC'C, det_one]
  have hback : ∀ v w : Matrix (Fin 3) (Fin 3) K, C' * v * C = C' * w * C → v = w := by
    intro v w h
    have e : ∀ v : Matrix (Fin 3) (Fin 3) K, C * (C' * v * C) * C' = v := fun v => by
      calc C * (C' * v * C) * C' = (C * C') * v * (C * C') := by simp only [Matrix.mul_assoc]
        _ = v := by rw [hCC', Matrix.one_mul, Matrix.mul_one]
    rw [← e v, ← e w, h]
  have hentries : ∀ (e : Fin 3 → K), diagonal e * diagonal e = 1 → ∀ i, e i * e i = 1 := by
    intro e he i
    have := congrFun (congrFun he i) i
    simpa [diagonal_mul_diagonal] using this
  have hprod : ∀ (e : Fin 3 → K), (diagonal e).det = 1 → e 0 * e 1 * e 2 = 1 := by
    intro e he
    rwa [det_diagonal, Fin.prod_univ_three] at he
  have hnot1 : ∀ (v : Matrix (Fin 3) (Fin 3) K) (e : Fin 3 → K), C' * v * C = diagonal e →
      v ≠ 1 → ¬ ∀ i, e i = 1 := by
    intro v e hve hv he
    apply hv
    apply hback
    rw [hve, Matrix.mul_one, hC'C]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [he i]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have ha := hentries a (by rw [← hea]; exact hsq v₁ hv₁)
  have hb := hentries b (by rw [← heb]; exact hsq v₂ hv₂)
  have had := hprod a (by rw [← hea]; exact hdet v₁ hd₁)
  have hbd := hprod b (by rw [← heb]; exact hdet v₂ hd₂)
  have hab : a ≠ b := by
    intro h
    apply h₁₂
    apply hback
    rw [hea, heb, h]
  have hc : ∀ v : Matrix (Fin 3) (Fin 3) K, g * v = v * g →
      C' * g * C * (C' * v * C) = C' * v * C * (C' * g * C) := by
    intro v hv
    rw [conj_mul_conj hCC', conj_mul_conj hCC', hv]
  have hgdiag : IsDiag3 (C' * g * C) := by
    intro i j hij
    rcases separate_of_involutions h2 ha hb had hbd (hnot1 v₁ a hea h₁) (hnot1 v₂ b heb h₂)
      hab hij with hij' | hij'
    · exact offDiag_eq_zero_of_commute_diagonal (by rw [← hea]; exact hc v₁ hg₁) hij'
    · exact offDiag_eq_zero_of_commute_diagonal (by rw [← heb]; exact hc v₂ hg₂) hij'
  have hyd : IsDiag3 (C' * y * C) := by
    rw [hyδ]
    intro i j hij
    exact diagonal_apply_ne _ hij
  exact commute_of_conj hCC' (hgdiag.commute hyd)

theorem eq_one_of_conj_eq_smul {g g' s : Matrix (Fin 3) (Fin 3) K} (hgg' : g' * g = 1)
    (hs : s.trace ≠ 0) {c : K} (h : g * s * g' = c • s) : c = 1 := by
  have htr : (g * s * g').trace = s.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hgg', Matrix.one_mul]
  rw [h, Matrix.trace_smul, smul_eq_mul] at htr
  have : (c - 1) * s.trace = 0 := by rw [sub_mul, htr, one_mul, sub_self]
  rcases mul_eq_zero.1 this with h' | h'
  · exact sub_eq_zero.1 h'
  · exact absurd h' hs

theorem two_mul_add_inv_ne_zero (h3 : (3 : K) ≠ 0) {a : K} (ha9 : a ^ 9 = 1) :
    a + a + a⁻¹ * a⁻¹ ≠ 0 := by
  intro h
  have ha0 : a ≠ 0 := by
    rintro rfl
    norm_num at ha9
  have h' : 2 * a ^ 3 + 1 = 0 := by
    have : a ^ 2 * (a + a + a⁻¹ * a⁻¹) = 2 * a ^ 3 + 1 := by
      field_simp
      ring
    rw [← this, h, mul_zero]
  apply h3
  have h9 : (3 : K) * 3 = 0 := by
    linear_combination (-8) * ha9 + (4 * a ^ 6 - 2 * a ^ 3 + 1) * h'
  exact mul_self_eq_zero.1 h9

end CFSG.Quasithin.F134.LieOdd
