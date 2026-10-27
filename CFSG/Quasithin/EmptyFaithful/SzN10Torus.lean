module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin

open Matrix

section Torus

variable {F : Type} [Field F]

@[expose] def szN10_diag (t : Fˣ) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two_of]⟩

theorem szN10_diag_one_zero (t : Fˣ) :
    ((szN10_diag t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  simp [szN10_diag]

@[expose] def szN10_diagHom : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun := szN10_diag
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [szN10_diag]
  map_mul' a b := by
    show szN10_diag (a * b) = szN10_diag a * szN10_diag b
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [szN10_diag, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem szN10_diag_mulVec (s : Fˣ) (w : Fin 2 → F) :
    ((szN10_diag s : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec w 0 =
        (s : F) * w 0 ∧
      ((szN10_diag s : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec w 1 =
        ((s⁻¹ : Fˣ) : F) * w 1 := by
  simp [szN10_diag, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem szN10_diag_fix {s : Fˣ} {w : Fin 2 → F} (hw0 : w ≠ 0)
    (hw : ((szN10_diag s : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).mulVec w = w) : s = 1 := by
  obtain ⟨h0, h1⟩ := szN10_diag_mulVec s w
  rw [hw] at h0 h1
  by_cases hw0' : w 0 = 0
  · have hw1 : w 1 ≠ 0 := by
      intro hw1
      apply hw0
      funext i
      fin_cases i
      · exact hw0'
      · exact hw1
    have h2 : ((s⁻¹ : Fˣ) : F) = 1 := by
      have : ((s⁻¹ : Fˣ) : F) * w 1 = 1 * w 1 := by rw [one_mul]; exact h1.symm
      exact mul_right_cancel₀ hw1 this
    have h3 : s⁻¹ = 1 := Units.ext h2
    exact inv_eq_one.mp h3
  · have h2 : (s : F) = 1 := by
      have : (s : F) * w 0 = 1 * w 0 := by rw [one_mul]; exact h0.symm
      exact mul_right_cancel₀ hw0' this
    exact Units.ext h2

theorem szN10_card_dvd_of_pow_eq_one [Fintype F] (h : ∀ t : Fˣ, t ^ 72 = 1) :
    Fintype.card F - 1 ∣ 72 := by
  have h1 : Monoid.exponent Fˣ ∣ 72 := Monoid.exponent_dvd_of_forall_pow_eq_one h
  rw [IsCyclic.exponent_eq_card, Nat.card_units, Nat.card_eq_fintype_card] at h1
  exact h1

theorem szN10_n_eq_two_of_pow_eq_one [Fintype F] {n : ℕ} (hn : 1 < n)
    (hcard : Fintype.card F = 2 ^ n) (h : ∀ t : Fˣ, t ^ 72 = 1) : n = 2 := by
  have hd := szN10_card_dvd_of_pow_eq_one h
  rw [hcard] at hd
  have hle : 2 ^ n - 1 ≤ 72 := Nat.le_of_dvd (by norm_num) hd
  have hn6 : n ≤ 6 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  interval_cases n <;> simp_all

end Torus

end CFSG.Quasithin
