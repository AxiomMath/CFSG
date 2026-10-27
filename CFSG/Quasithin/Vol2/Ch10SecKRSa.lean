module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open Matrix

abbrev SL5 : Type := Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

@[expose] def btSL (b : Fin 5 → ℕ) : Subgroup SL5 where
  carrier := {A | (A : Matrix (Fin 5) (Fin 5) (ZMod 2)).BlockTriangular b}
  one_mem' := blockTriangular_one
  mul_mem' := fun ha hb => ha.mul hb
  inv_mem' := fun hx => C10P4F.inv_mem_of_mul_closed
    (S := {A : SL5 | (A : Matrix (Fin 5) (Fin 5) (ZMod 2)).BlockTriangular b})
    blockTriangular_one (fun _ _ ha hb => ha.mul hb) hx

theorem mem_btSL {b : Fin 5 → ℕ} {A : SL5} :
    A ∈ btSL b ↔ (A : Matrix (Fin 5) (Fin 5) (ZMod 2)).BlockTriangular b := Iff.rfl

abbrev P0 : Subgroup SL5 := btSL ![0, 0, 1, 2, 3]

abbrev P2 : Subgroup SL5 := btSL ![0, 1, 2, 2, 3]

abbrev P013 : Subgroup SL5 := btSL ![0, 0, 1, 1, 2]

theorem P0_le : P0 ≤ P013 := fun A hA i j h => hA (by
  fin_cases i <;> fin_cases j <;> simp_all)

theorem P2_le : P2 ≤ P013 := fun A hA i j h => hA (by
  fin_cases i <;> fin_cases j <;> simp_all)

theorem mul_apply_five (M N : Matrix (Fin 5) (Fin 5) (ZMod 2)) (i j : Fin 5) :
    (M * N) i j = M i 0 * N 0 j + M i 1 * N 1 j + M i 2 * N 2 j + M i 3 * N 3 j +
      M i 4 * N 4 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_five]

theorem eq_one_of_mul_eq_one {a b : ZMod 2} (h : a * b = 1) : a = 1 := by
  revert a b h
  decide

section Entries

variable {x y : SL5}

theorem P2_zero (hx : x ∈ P2) {i j : Fin 5} (h : (![0, 1, 2, 2, 3] : Fin 5 → ℕ) j <
    (![0, 1, 2, 2, 3] : Fin 5 → ℕ) i) : (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j = 0 := hx h

theorem P2_diag (hx : x ∈ P2) :
    (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 0 = 1 ∧
      (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 1 = 1 := by
  have hi : x⁻¹ ∈ P2 := P2.inv_mem hx
  have h1 : ((x * x⁻¹ : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by rw [mul_inv_cancel]; rfl
  have e00 := congrFun (congrFun h1 0) 0
  have e11 := congrFun (congrFun h1 1) 1
  rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply_five] at e00 e11
  simp only [P2_zero hx (i := 1) (j := 0) (by decide), P2_zero hi (i := 1) (j := 0) (by decide),
    P2_zero hi (i := 2) (j := 0) (by decide), P2_zero hi (i := 3) (j := 0) (by decide),
    P2_zero hi (i := 4) (j := 0) (by decide), P2_zero hi (i := 2) (j := 1) (by decide),
    P2_zero hi (i := 3) (j := 1) (by decide), P2_zero hi (i := 4) (j := 1) (by decide),
    mul_zero, zero_mul, add_zero, zero_add, Matrix.one_apply_eq] at e00 e11
  exact ⟨eq_one_of_mul_eq_one e00, eq_one_of_mul_eq_one e11⟩

theorem P2_entry01_mul (hx : x ∈ P2) (hy : y ∈ P2) :
    ((x * y : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 1 =
      (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 1 + (y : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply_five, (P2_diag hx).1, (P2_diag hy).2,
    P2_zero hy (i := 2) (j := 1) (by decide), P2_zero hy (i := 3) (j := 1) (by decide),
    P2_zero hy (i := 4) (j := 1) (by decide)]
  ring

theorem entry01_eq_zero_of_pow_three (hx : x ∈ P2) (h3 : x ^ 3 = 1) :
    (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 1 = 0 := by
  have hx2 : x * x ∈ P2 := P2.mul_mem hx hx
  have h := congrArg (fun z : SL5 => (z : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 1) h3
  simp only [pow_succ, pow_zero, one_mul] at h
  rw [P2_entry01_mul hx2 hx, P2_entry01_mul hx hx] at h
  have h1 : (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 1 = 0 := by decide
  rw [show ((1 : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 from rfl, h1] at h
  have key : ∀ a : ZMod 2, a + a + a = 0 → a = 0 := by decide
  exact key _ h

end Entries

theorem conj_mem_P2_of_mem_P0 {g x : SL5} (hg : g ∈ P0) (hx : x ∈ P2) (h3 : x ^ 3 = 1) :
    g * x * g⁻¹ ∈ P2 := by
  have h01 := entry01_eq_zero_of_pow_three hx h3
  obtain ⟨h00, h11⟩ := P2_diag hx
  have hy : g * x * g⁻¹ ∈ P013 :=
    P013.mul_mem (P013.mul_mem (P0_le hg) (P2_le hx)) (P013.inv_mem (P0_le hg))
  have hgi : g⁻¹ ∈ P013 := P013.inv_mem (P0_le hg)
  intro i j hij
  by_cases h10 : i = 1 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h10
    have hgg : ((g * g⁻¹ : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 0 = 0 := by
      rw [mul_inv_cancel]; decide
    rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply_five] at hgg
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mul_apply_five]
    simp only [mul_apply_five]
    have z1 := hx (i := 1) (j := 0) (by decide)
    have z2 := hx (i := 2) (j := 0) (by decide)
    have z3 := hx (i := 3) (j := 0) (by decide)
    have z4 := hx (i := 4) (j := 0) (by decide)
    have z5 := hx (i := 2) (j := 1) (by decide)
    have z6 := hx (i := 3) (j := 1) (by decide)
    have z7 := hx (i := 4) (j := 1) (by decide)
    have w2 := hgi (i := 2) (j := 0) (by decide)
    have w3 := hgi (i := 3) (j := 0) (by decide)
    have w4 := hgi (i := 4) (j := 0) (by decide)
    simp only [z1, z2, z3, z4, z5, z6, z7, w2, w3, w4, h00, h11, h01, mul_zero, add_zero,
      zero_add, mul_one] at hgg ⊢
    exact hgg
  · apply hy
    fin_cases i <;> fin_cases j <;> simp_all

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
