module

public import CFSG.Quasithin.Vol2.Ch10SecKRSb
public import CFSG.Quasithin.Vol2.Ch10SecQ9H18
public import CFSG.Quasithin.Background.F918T0

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag C10P4F

theorem fix_vec_of_uniSL {v : Fin 5 → ZMod 2}
    (h : ∀ g ∈ uniSL 5, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v) :
    v = 0 ∨ v = Pi.single 0 1 := by
  have key : ∀ (i j : Fin 5) (hij : i < j), v j = 0 := by
    intro i j hij
    have h1 := h _ (trvE_mem_uniSL i j hij)
    rw [← smul_eq_mulVec', trvE_mulVec] at h1
    have h2 := congrFun h1 i
    simpa using h2
  have h1 := key 0 1 (by decide)
  have h2 := key 0 2 (by decide)
  have h3 := key 0 3 (by decide)
  have h4 := key 0 4 (by decide)
  rcases zmod2_cases (v 0) with h0 | h0
  · left
    funext k
    fin_cases k <;> simp_all
  · right
    funext k
    fin_cases k <;> simp_all

theorem mem_Q1_iff_mulVec {g : SL5} :
    (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 ↔ g ∈ Q1 := by
  rw [mem_Q1_iff]
  constructor
  · intro h a ha
    have := congrFun h a
    have ha0 : a ≠ 0 := fun h0 => by rw [h0] at ha; simp at ha
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, ha0] using this
  · intro h
    have hcol : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single 0 1 =
        (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 0 • Pi.single 0 1 := by
      funext a
      by_cases ha : a = 0
      · subst ha
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      · have ha1 : 1 ≤ (a : ℕ) := by
          rcases Nat.eq_zero_or_pos (a : ℕ) with h0 | h0
          · exact absurd (Fin.ext h0) ha
          · exact h0
        simp [Matrix.mulVec, dotProduct, Pi.single_apply, ha, h a ha1]
    have hne := mulVec_ne_zero g (x := Pi.single (0 : Fin 5) (1 : ZMod 2)) (by simp)
    rcases zmod2_cases ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 0) with h0 | h0
    · rw [hcol, h0, zero_smul] at hne
      exact absurd rfl hne
    · rw [hcol, h0, one_smul]

theorem trvE_conj_apply {n : ℕ} (i j : Fin n) (h : i ≠ j) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (b : Fin n) (hb : b ≠ i) :
    (((trvE i j h : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
      B * ((trvE i j h : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) i b = B i b + B j b := by
  simp only [trvE, trv, Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.add_apply, Matrix.transpose_vecMulVec]
  simp [Matrix.mul_apply, vecMulVec_apply, Pi.single_apply, hb]

theorem row_eq_zero_of_trvE {n : ℕ} {i j : Fin n} (h : i ≠ j) {B : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hB : ((trvE i j h : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) * B *
      ((trvE i j h : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = B) {b : Fin n} (hb : b ≠ i) : B j b = 0 := by
  have h1 := trvE_conj_apply i j h B b hb
  rw [hB] at h1
  have h2 : ∀ x y : ZMod 2, x = x + y → y = 0 := by decide
  exact h2 _ _ h1

@[expose] def B0 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0]

theorem fix_alt_of_uniSL {B : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hB : B ∈ altMat 5)
    (h : ∀ g ∈ uniSL 5, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * B *
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = B) : B = 0 ∨ B = B0 := by
  obtain ⟨hB1, hB2⟩ := mem_altMat.mp hB
  have hsym : ∀ a b, B a b = B b a := fun a b => by
    have := congrFun (congrFun hB1 b) a
    simpa using this
  have hr : ∀ (i j : Fin 5) (hij : i < j) (b : Fin 5), b ≠ i → B j b = 0 := fun i j hij b hb =>
    row_eq_zero_of_trvE (ne_of_lt hij) (h _ (trvE_mem_uniSL i j hij)) hb
  have r1 : ∀ b : Fin 5, b ≠ 0 → B 1 b = 0 := hr 0 1 (by decide)
  have r2 : ∀ b : Fin 5, B 2 b = 0 := fun b => by
    by_cases hb : b = 0
    · exact hr 1 2 (by decide) b (by rw [hb]; decide)
    · exact hr 0 2 (by decide) b hb
  have r3 : ∀ b : Fin 5, B 3 b = 0 := fun b => by
    by_cases hb : b = 0
    · exact hr 1 3 (by decide) b (by rw [hb]; decide)
    · exact hr 0 3 (by decide) b hb
  have r4 : ∀ b : Fin 5, B 4 b = 0 := fun b => by
    by_cases hb : b = 0
    · exact hr 1 4 (by decide) b (by rw [hb]; decide)
    · exact hr 0 4 (by decide) b hb
  have r0 : ∀ b : Fin 5, b ≠ 1 → B 0 b = 0 := fun b hb => by
    rw [hsym]
    fin_cases b
    · exact hB2 0
    · exact absurd rfl hb
    · exact r2 0
    · exact r3 0
    · exact r4 0
  have e01 := hsym 0 1
  clear hsym hr h hB1 hB
  rcases zmod2_cases (B 1 0) with h0 | h0
  · left
    ext a b
    fin_cases a <;> fin_cases b <;> simp [r0, r1, r2, r3, r4, h0, e01]
  · right
    ext a b
    fin_cases a <;> fin_cases b <;> simp [r0, r1, r2, r3, r4, h0, e01, B0]

theorem conj_B0_apply (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) (a b : Fin 5) :
    (g * B0 * gᵀ) a b = g a 0 * g b 1 + g a 1 * g b 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_five, B0]
  ring

theorem eq_zero_of_conj_B0 {g : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : g * B0 * gᵀ = B0)
    {a : Fin 5} (ha : 2 ≤ (a : ℕ)) : g a 0 = 0 ∧ g a 1 = 0 := by
  have e0 := congrFun (congrFun h a) 0
  have e1 := congrFun (congrFun h a) 1
  have d := congrFun (congrFun h 0) 1
  rw [conj_B0_apply] at e0 e1 d
  have hB0 : ∀ b : Fin 5, B0 a b = 0 := fun b => by
    fin_cases a <;> simp at ha <;> fin_cases b <;> rfl
  rw [hB0] at e0 e1
  have key : ∀ x y p q r s : ZMod 2, x * q + y * p = 0 → x * s + y * r = 0 →
      p * s + q * r = 1 → x = 0 ∧ y = 0 := by decide
  exact key _ _ _ _ _ _ e0 e1 (by simpa [B0] using d)

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
