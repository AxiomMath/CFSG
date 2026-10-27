module

public import CFSG.Quasithin.Vol2.Ch4Sec3C136Off1

public section

namespace CFSG.Quasithin.H13.Ch4

open Matrix

variable {F : Type} [Field F]

@[expose] def tens (c : Matrix (Fin 2) (Fin 2) F) (P : Matrix (Fin 3) (Fin 3) F)
    (v : Fin 2 → Fin 3 → F) : Fin 2 → Fin 3 → F :=
  fun i => ∑ j, c i j • P.mulVec (v j)

theorem tens_apply (c : Matrix (Fin 2) (Fin 2) F) (P : Matrix (Fin 3) (Fin 3) F)
    (v : Fin 2 → Fin 3 → F) (i : Fin 2) : tens c P v i = ∑ j, c i j • P.mulVec (v j) := rfl

theorem tens_single (c : Matrix (Fin 2) (Fin 2) F) (P : Matrix (Fin 3) (Fin 3) F) (l : Fin 2)
    (x : Fin 3 → F) (i : Fin 2) : tens c P (Pi.single l x) i = c i l • P.mulVec x := by
  classical
  rw [tens_apply, Finset.sum_eq_single l]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, Matrix.mulVec_zero, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem tens_tens (c c' : Matrix (Fin 2) (Fin 2) F) (P P' : Matrix (Fin 3) (Fin 3) F)
    (v : Fin 2 → Fin 3 → F) : tens c P (tens c' P' v) = tens (c * c') (P * P') v := by
  funext i
  simp only [tens_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.smul_sum, smul_smul,
    Matrix.mul_apply, Finset.sum_smul, Matrix.mulVec_mulVec]
  rw [Finset.sum_comm]

theorem tens_one_one (v : Fin 2 → Fin 3 → F) : tens 1 1 v = v := by
  funext i
  rw [tens_apply, Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_smul, Matrix.one_mulVec]
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem tens_one (P : Matrix (Fin 3) (Fin 3) F) (v : Fin 2 → Fin 3 → F) :
    tens 1 P v = dact P v := by
  funext i
  rw [tens_apply, Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_smul]
    rfl
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem tens_smul_smul (c : Matrix (Fin 2) (Fin 2) F) (P : Matrix (Fin 3) (Fin 3) F) {r : F}
    (hr : r ≠ 0) (v : Fin 2 → Fin 3 → F) : tens (r⁻¹ • c) (r • P) v = tens c P v := by
  funext i
  simp only [tens_apply, Matrix.smul_apply, Matrix.smul_mulVec, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, mul_comm (r⁻¹) (c i j), mul_assoc, inv_mul_cancel₀ hr, mul_one]

theorem matrix_eq_of_mulVec_eq {A B : Matrix (Fin 3) (Fin 3) F} (h : ∀ x, A.mulVec x = B.mulVec x) :
    A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h])

theorem exists_mulVec_ne_zero {A : Matrix (Fin 3) (Fin 3) F} (h : A ≠ 0) : ∃ x, A.mulVec x ≠ 0 := by
  by_contra hx
  push Not at hx
  exact h (matrix_eq_of_mulVec_eq fun x => by rw [hx x, Matrix.zero_mulVec])

section CharTwo

variable [CharP F 2]

theorem eq_one_of_mul_self_eq_one {x : F} (h : x * x = 1) : x = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : (x - 1) * (x - 1) = 0 := by linear_combination h + (1 - x) * h2
  have h4 := mul_self_eq_zero.mp h3
  exact sub_eq_zero.mp h4

theorem trace_eq_one_of_mul_self {P : Matrix (Fin 3) (Fin 3) F} (h : P * P = 1) : P.trace = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have htr : P.trace * P.trace = (P * P).trace := by
    rw [Matrix.trace_fin_three, Matrix.trace_fin_three]
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (P 0 0 * P 1 1 + P 0 0 * P 2 2 + P 1 1 * P 2 2 - P 0 1 * P 1 0 -
      P 0 2 * P 2 0 - P 1 2 * P 2 1) * h2
  have h1 : (1 : Matrix (Fin 3) (Fin 3) F).trace = 1 := by
    rw [Matrix.trace_one, Fintype.card_fin]
    linear_combination h2
  rw [h, h1] at htr
  exact eq_one_of_mul_self_eq_one htr

theorem det_eq_one_of_mul_self {P : Matrix (Fin 3) (Fin 3) F} (h : P * P = 1) : P.det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h1
  exact eq_one_of_mul_self_eq_one h1

variable [Finite F]

theorem exists_normalized {e : Equiv.Perm (Fin 2 → Fin 3 → F)} (hadd : e ∈ addPerms F)
    (hlin : e ∈ linPerms F) (hn : NormalizesDact ⇑e) (hn' : NormalizesDact ⇑e⁻¹)
    (hinv : e * e = 1) :
    ∃ (c : Matrix (Fin 2) (Fin 2) F) (P : Matrix (Fin 3) (Fin 3) F), c * c = 1 ∧ P * P = 1 ∧
      ∀ v, e v = tens c P v := by
  classical
  obtain ⟨P₀, c₀, hT⟩ := exists_matrix_normalForm (T := toAddEquivOf e hadd) two_ne_zero hn hn'
    (fun μ v => hlin μ v)
  have he : ∀ v, e v = tens c₀ P₀ v := fun v => funext fun i => hT v i
  have hsq : ∀ v, tens (c₀ * c₀) (P₀ * P₀) v = v := by
    intro v
    rw [← tens_tens, ← he, ← he]
    exact congrArg (fun f : Equiv.Perm (Fin 2 → Fin 3 → F) => f v) hinv
  have hent : ∀ (i l : Fin 2) (x : Fin 3 → F),
      (c₀ * c₀) i l • (P₀ * P₀).mulVec x = (Pi.single l x : Fin 2 → Fin 3 → F) i := by
    intro i l x
    rw [← tens_single, hsq]
  set d := (c₀ * c₀) 0 0 with hd
  have hd0 : d ≠ 0 := by
    intro h0
    have h1 := congrFun (hent 0 0 (Pi.single 0 1)) 0
    rw [← hd, h0, zero_smul] at h1
    simp at h1
  have hPv : ∀ x, (P₀ * P₀).mulVec x = d⁻¹ • x := by
    intro x
    have h1 : d • (P₀ * P₀).mulVec x = x := by
      have h2 := hent 0 0 x
      rwa [← hd, Pi.single_eq_same] at h2
    calc (P₀ * P₀).mulVec x = d⁻¹ • (d • (P₀ * P₀).mulVec x) := by
          rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
      _ = d⁻¹ • x := by rw [h1]
  have hPm : P₀ * P₀ = d⁻¹ • (1 : Matrix (Fin 3) (Fin 3) F) :=
    matrix_eq_of_mulVec_eq fun x => by rw [hPv, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcm : c₀ * c₀ = d • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i l
    have h2 := congrFun (hent i l (Pi.single 0 1)) 0
    rw [hPv, smul_smul] at h2
    rw [Matrix.smul_apply, smul_eq_mul]
    by_cases hil : i = l
    · subst hil
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h2
      rw [Matrix.one_apply_eq, mul_one]
      calc (c₀ * c₀) i i = (c₀ * c₀) i i * d⁻¹ * d := by
            rw [mul_assoc, inv_mul_cancel₀ hd0, mul_one]
        _ = d := by rw [h2, one_mul]
    · rw [Pi.single_eq_of_ne hil] at h2
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.zero_apply] at h2
      rw [Matrix.one_apply_ne hil, mul_zero]
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h (inv_ne_zero hd0)
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) d
  have hr0 : r ≠ 0 := fun h0 => hd0 (by rw [hr, h0, mul_zero])
  refine ⟨r⁻¹ • c₀, r • P₀, ?_, ?_, fun v => by rw [he, tens_smul_smul c₀ P₀ hr0]⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcm, smul_smul, hr]
    have h1 : r⁻¹ * r⁻¹ * (r * r) = 1 := by field_simp
    rw [h1, one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hPm, smul_smul, hr]
    have h1 : r * r * (r * r)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero hr0 hr0)
    rw [h1, one_smul]

omit [CharP F 2] [Finite F] in
theorem ne_zero_of_mul_self_eq_one {n : ℕ} [NeZero n] {A : Matrix (Fin n) (Fin n) F}
    (h : A * A = 1) : A ≠ 0 := by
  intro h0
  rw [h0, zero_mul] at h
  have := congrFun (congrFun h 0) 0
  simp at this

omit [Finite F] in
theorem normalized_unique {c c' : Matrix (Fin 2) (Fin 2) F} {P P' : Matrix (Fin 3) (Fin 3) F}
    (hc : c * c = 1) (hP : P * P = 1) (hP' : P' * P' = 1) (h : ∀ v, tens c P v = tens c' P' v) :
    c = c' ∧ P = P' := by
  classical
  have hent : ∀ (i l : Fin 2) (x : Fin 3 → F), c i l • P.mulVec x = c' i l • P'.mulVec x := by
    intro i l x
    rw [← tens_single, ← tens_single, h]
  obtain ⟨i, l, hil⟩ : ∃ i l, c i l ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ne_zero_of_mul_self_eq_one hc (Matrix.ext hcon)
  have hil' : c' i l ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_mulVec_ne_zero (ne_zero_of_mul_self_eq_one hP)
    have h1 := hent i l x
    rw [h0, zero_smul] at h1
    exact hx (smul_eq_zero.mp h1 |>.resolve_left hil)
  set s := c i l / c' i l with hs
  have hPP : P' = s • P := by
    apply matrix_eq_of_mulVec_eq
    intro x
    have h1 := hent i l x
    rw [Matrix.smul_mulVec, hs, div_eq_mul_inv, mul_comm, ← smul_smul, h1, smul_smul,
      inv_mul_cancel₀ hil', one_smul]
  have hs1 : s = 1 := by
    have h1 : P' * P' = (s * s) • (P * P) := by
      rw [hPP, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hP', hP] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
    exact eq_one_of_mul_self_eq_one h2.symm
  rw [hs1, one_smul] at hPP
  subst hPP
  refine ⟨?_, rfl⟩
  obtain ⟨x, hx⟩ := exists_mulVec_ne_zero (ne_zero_of_mul_self_eq_one hP)
  ext a b
  exact smul_left_injective F hx (hent a b x)

omit [Finite F] in
theorem commute_of_commute {c c' : Matrix (Fin 2) (Fin 2) F} {P P' : Matrix (Fin 3) (Fin 3) F}
    (hc : c * c = 1) (hc' : c' * c' = 1) (hP : P * P = 1) (hP' : P' * P' = 1)
    (h : ∀ v, tens (c * c') (P * P') v = tens (c' * c) (P' * P) v) :
    c * c' = c' * c ∧ P * P' = P' * P := by
  classical
  have hent : ∀ (i l : Fin 2) (x : Fin 3 → F),
      (c * c') i l • (P * P').mulVec x = (c' * c) i l • (P' * P).mulVec x := by
    intro i l x
    rw [← tens_single, ← tens_single, h]
  have hcc : (c * c') * (c' * c) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc c' c' c, hc', Matrix.one_mul, hc]
  have hPP : (P * P') * (P' * P) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P' P' P, hP', Matrix.one_mul, hP]
  have hne : P * P' ≠ 0 := fun h0 => by
    rw [h0, Matrix.zero_mul] at hPP
    have := congrFun (congrFun hPP 0) 0
    simp at this
  have hne' : P' * P ≠ 0 := fun h0 => by
    rw [h0, Matrix.mul_zero] at hPP
    have := congrFun (congrFun hPP 0) 0
    simp at this
  obtain ⟨i, l, hil⟩ : ∃ i l, (c * c') i l ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : c * c' = 0 := Matrix.ext hcon
    rw [h0, Matrix.zero_mul] at hcc
    have := congrFun (congrFun hcc 0) 0
    simp at this
  have hil' : (c' * c) i l ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_mulVec_ne_zero hne
    have h1 := hent i l x
    rw [h0, zero_smul] at h1
    exact hx (smul_eq_zero.mp h1 |>.resolve_left hil)
  set s := (c * c') i l / (c' * c) i l with hs
  have hrel : P' * P = s • (P * P') := by
    apply matrix_eq_of_mulVec_eq
    intro x
    have h1 := hent i l x
    rw [Matrix.smul_mulVec, hs, div_eq_mul_inv, mul_comm, ← smul_smul, h1, smul_smul,
      inv_mul_cancel₀ hil', one_smul]
  have hconj : P' * P * P' = s • P := by
    rw [hrel, Matrix.smul_mul, Matrix.mul_assoc, hP', Matrix.mul_one]
  have htr : P.trace = s * P.trace := by
    have h1 := congrArg Matrix.trace hconj
    rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_cycle, hP', Matrix.one_mul] at h1
    exact h1
  rw [trace_eq_one_of_mul_self hP, mul_one] at htr
  have hs1 : s = 1 := htr.symm
  rw [hs1, one_smul] at hrel
  refine ⟨?_, hrel.symm⟩
  obtain ⟨x, hx⟩ := exists_mulVec_ne_zero hne
  ext a b
  have h1 := hent a b x
  rw [hrel] at h1
  exact smul_left_injective F hx h1

end CharTwo

end CFSG.Quasithin.H13.Ch4
