module

public import CFSG.Quasithin.Vol2.Ch10SecQ6O4c
public import CFSG.Quasithin.Vol2.Ch10SecQ6SL2b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Matrix

variable {F : Type} [Field F]

@[expose] def hterm (n : ℕ) (g : SpecialLinearGroup (Fin 2) F) (c : F) :
    Matrix (Fin 2) (Fin 2) F :=
  (g : Matrix (Fin 2) (Fin 2) F) * !![c, 0; 0, 0] * (frobPow n (g : Matrix (Fin 2) (Fin 2) F))ᵀ

theorem conj_apply (n : ℕ) (g : Matrix (Fin 2) (Fin 2) F) (X : Matrix (Fin 2) (Fin 2) F)
    (i j : Fin 2) : (g * X * (frobPow n g)ᵀ) i j =
      ∑ k, ∑ l, g i k * X k l * sig n (g j l) := by
  simp only [mul_apply, transpose_apply, frobPow, map_apply, sig, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem conj_entry (n : ℕ) (g X : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    (g * X * (frobPow n g)ᵀ : Matrix (Fin 2) (Fin 2) F) i j =
      g i 0 * X 0 0 * sig n (g j 0) + g i 0 * X 0 1 * sig n (g j 1) +
        (g i 1 * X 1 0 * sig n (g j 0) + g i 1 * X 1 1 * sig n (g j 1)) := by
  rw [conj_apply]
  simp [Fin.sum_univ_two]

theorem eq_zero_of_mul_sig [Finite F] {n : ℕ} (hF : Nat.card F = 4 ^ n) {x : F}
    (h : x * sig n x = 0) : x = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact sig_injective hF (h.trans (sig_zero n).symm)

theorem eq_one_of_herm_fix [CharP F 2] [Finite F] {n : ℕ} (hF : Nat.card F = 4 ^ n)
    {g : SpecialLinearGroup (Fin 2) F}
    (h : ∀ X, IsHerm n X → (g : Matrix (Fin 2) (Fin 2) F) * X *
      (frobPow n (g : Matrix (Fin 2) (Fin 2) F))ᵀ = X) : g = 1 := by
  set G := (g : Matrix (Fin 2) (Fin 2) F) with hG
  have h1 := h !![1, 0; 0, 0] (isHerm_iff.mpr ⟨by simp [sig_one], by simp [sig_zero],
    by simp [sig_zero], by simp [sig_zero]⟩)
  have h2 := h !![0, 0; 0, 1] (isHerm_iff.mpr ⟨by simp [sig_zero], by simp [sig_one],
    by simp [sig_zero], by simp [sig_zero]⟩)
  have h3 := h !![0, 1; 1, 0] (isHerm_iff.mpr ⟨by simp [sig_zero], by simp [sig_zero],
    by simp [sig_one], by simp [sig_one]⟩)
  have a11 : G 1 0 * sig n (G 1 0) = 0 := by
    have h := congrFun (congrFun h1 1) 1
    rw [conj_entry] at h
    simpa using h
  have a00 : G 0 0 * sig n (G 0 0) = 1 := by
    have h := congrFun (congrFun h1 0) 0
    rw [conj_entry] at h
    simpa using h
  have b00 : G 0 1 * sig n (G 0 1) = 0 := by
    have h := congrFun (congrFun h2 0) 0
    rw [conj_entry] at h
    simpa using h
  have b11 : G 1 1 * sig n (G 1 1) = 1 := by
    have h := congrFun (congrFun h2 1) 1
    rw [conj_entry] at h
    simpa using h
  have c01 : G 0 0 * sig n (G 1 1) + G 0 1 * sig n (G 1 0) = 1 := by
    have h := congrFun (congrFun h3 0) 1
    rw [conj_entry] at h
    simpa using h
  have hc := eq_zero_of_mul_sig hF a11
  have hb := eq_zero_of_mul_sig hF b00
  rw [hb, zero_mul, add_zero] at c01
  have hdet : G 0 0 * G 1 1 = 1 := by
    have h := g.2
    rw [det_fin_two, ← hG, hb, zero_mul, sub_zero] at h
    exact h
  have hσ11 : sig n (G 1 1) ≠ 0 := fun h => by
    rw [h, mul_zero] at b11
    exact zero_ne_one b11
  have hd : G 0 0 = G 1 1 := mul_right_cancel₀ hσ11 (c01.trans b11.symm)
  have ha : G 0 0 = 1 := eq_one_of_sq_eq_one_char_two (by
    rw [sq]
    nth_rewrite 2 [hd]
    exact hdet)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_one, ← hG]
  fin_cases i <;> fin_cases j
  · simpa using ha
  · simpa using hb
  · simpa using hc
  · simpa [← hd] using ha

theorem eq_E11_of_ut_fix [CharP F 2] [Finite F] {n : ℕ} (hF : Nat.card F = 4 ^ n) (hn : 1 ≤ n)
    {X : Matrix (Fin 2) (Fin 2) F} (hX : IsHerm n X)
    (h : ∀ t : F, ((ut t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * X *
      (frobPow n ((ut t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))ᵀ = X) :
    X = !![X 0 0, 0; 0, 0] := by
  obtain ⟨-, -, h01, -⟩ := isHerm_iff.mp hX
  have h11 : X 1 1 = 0 := by
    have h1 := congrFun (congrFun (h 1) 0) 1
    rw [conj_entry, coe_ut] at h1
    simpa [sig_one, sig_zero] using h1
  have hβ : X 0 1 = 0 := by
    refine eq_zero_of_trace hF hn fun t => ?_
    have h1 := congrFun (congrFun (h t) 0) 0
    rw [conj_entry, coe_ut] at h1
    simp [sig_one, h11, ← h01] at h1
    linear_combination h1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h11, hβ, ← h01, sig_zero]

theorem conj_ut_E11 (n : ℕ) (t : F) :
    ((ut t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 0, 0] *
      (frobPow n ((ut t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))ᵀ =
        !![1, 0; 0, 0] := by
  ext i j
  rw [conj_entry, coe_ut]
  fin_cases i <;> fin_cases j <;> simp [sig_one, sig_zero]

@[expose] def dg (l : F) (hl : l ≠ 0) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![l, 0; 0, l⁻¹], by simp [det_fin_two, hl]⟩

theorem conj_dg (n : ℕ) {l : F} (hl : l ≠ 0) (c : F) :
    ((dg l hl : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * !![c, 0; 0, 0] *
      (frobPow n ((dg l hl : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))ᵀ =
        !![l * sig n l * c, 0; 0, 0] := by
  ext i j
  rw [conj_entry]
  fin_cases i <;> fin_cases j <;> simp [dg, sig_zero]
  ring

@[expose] def jm [CharP F 2] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by simp [det_fin_two, CharTwo.neg_eq]⟩

@[expose] def vt (m : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; m, 1], by simp [det_fin_two]⟩

theorem herm_induction [CharP F 2] [Finite F] {n : ℕ} (hF : Nat.card F = 4 ^ n)
    {P : Matrix (Fin 2) (Fin 2) F → Prop} (hadd : ∀ X Y, P X → P Y → P (X + Y))
    (hT : ∀ (g : SpecialLinearGroup (Fin 2) F) (c : F), sig n c = c → P (hterm n g c))
    {X : Matrix (Fin 2) (Fin 2) F} (hX : IsHerm n X) : P X := by
  obtain ⟨h00, h11, -, h10⟩ := isHerm_iff.mp hX
  set m := X 1 0 with hm
  have hN : sig n (m * sig n m) = m * sig n m := by rw [sig_mul, sig_sig hF, mul_comm]
  have hsum : X = hterm n 1 (X 0 0) + hterm n jm (X 1 1) + hterm n (vt m) 1 + hterm n 1 1 +
      hterm n jm (m * sig n m) := by
    ext i j
    simp only [hterm, Matrix.add_apply, conj_entry]
    fin_cases i <;> fin_cases j <;> simp [jm, vt, sig_zero, sig_one]
    · rw [add_assoc, CharTwo.add_self_eq_zero (1 : F), add_zero]
    · exact h10.symm
    · exact hm.symm
    · rw [add_assoc, CharTwo.add_self_eq_zero (m * sig n m), add_zero]
  rw [hsum]
  exact hadd _ _ (hadd _ _ (hadd _ _ (hadd _ _ (hT 1 _ h00) (hT jm _ h11))
    (hT (vt m) 1 (sig_one n))) (hT 1 1 (sig_one n))) (hT jm _ hN)

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
