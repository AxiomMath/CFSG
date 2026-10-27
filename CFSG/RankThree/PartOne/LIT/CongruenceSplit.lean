module

public import CFSG.RankThree.PartOne.LIT.CongruenceFive
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix

@[expose] def splitForm (p : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod p) := !![0, 0, 1; 0, 2, 0; 1, 0, 0]

private theorem splitForm_two_ne_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')

theorem exists_diag_isotropic_zmod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b c : ZMod p} (ha : a ≠ 0)
    (hb : b ≠ 0) : ∃ x y : ZMod p, a * x ^ 2 + b * y ^ 2 + c = 0 := by
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]
    exact (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.C a * Polynomial.X ^ 2)
    (g := Polynomial.C b * Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C c)
    (Polynomial.degree_C_mul_X_pow 2 ha) (Polynomial.degree_quadratic hb) hodd
  exact ⟨x, y, by simpa [add_assoc] using hxy⟩

theorem diag_congr_splitForm {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (d : Fin 3 → ZMod p)
    (hd : ∀ i, d i ≠ 0) :
    ∃ (g : GL (Fin 3) (ZMod p)) (c : ZMod p), c ≠ 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * Matrix.diagonal d *
        (g : Matrix (Fin 3) (Fin 3) (ZMod p)) = c • splitForm p := by
  have h2 := splitForm_two_ne_zero hp
  obtain ⟨x, y, hxy⟩ := exists_diag_isotropic_zmod hp (c := d 2) (hd 0) (hd 1)
  set g : Matrix (Fin 3) (Fin 3) (ZMod p) :=
    !![d 0 * d 1 * x, 2 * d 1 * y, x; d 0 * d 1 * y, -(2 * d 0 * x), y; -(d 0 * d 1), 0, 1] with hg
  have hdetg : g.det = 4 * (d 0 * d 1 * d 2) := by
    rw [hg, det_fin_three]
    simp
    linear_combination (-4 * d 0 * d 1) * hxy
  have hdetne : g.det ≠ 0 := by
    rw [hdetg]
    exact mul_ne_zero (by rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2)
      (mul_ne_zero (mul_ne_zero (hd 0) (hd 1)) (hd 2))
  refine ⟨GeneralLinearGroup.mkOfDetNeZero g hdetne, -(2 * (d 0 * d 1 * d 2)),
    neg_ne_zero.mpr (mul_ne_zero h2 (mul_ne_zero (mul_ne_zero (hd 0) (hd 1)) (hd 2))), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hg, splitForm]
  · linear_combination (d 0 * d 1) ^ 2 * hxy
  · ring
  · linear_combination (d 0 * d 1) * hxy
  · ring
  · linear_combination (4 * d 0 * d 1) * hxy
  · ring
  · linear_combination (d 0 * d 1) * hxy
  · ring
  · linear_combination hxy

theorem exists_congr_splitForm {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (M : Matrix (Fin 3) (Fin 3) (ZMod p)) (hM : Mᵀ = M) (hdet : M.det ≠ 0) :
    ∃ (g : GL (Fin 3) (ZMod p)) (c : ZMod p), c ≠ 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M * (g : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        c • splitForm p := by
  obtain ⟨g₀, d, hd⟩ := exists_diagonal_congr (splitForm_two_ne_zero hp) M hM
  have hdiag : (Matrix.diagonal d).det ≠ 0 := by
    rw [← hd, det_mul, det_mul, det_transpose]
    exact mul_ne_zero (mul_ne_zero (GeneralLinearGroup.det_ne_zero g₀) hdet)
      (GeneralLinearGroup.det_ne_zero g₀)
  rw [det_diagonal] at hdiag
  have hd0 : ∀ i, d i ≠ 0 := fun i => Finset.prod_ne_zero_iff.mp hdiag i (Finset.mem_univ i)
  obtain ⟨g₁, c, hc, hg₁⟩ := diag_congr_splitForm hp d hd0
  refine ⟨g₀ * g₁, c, hc, ?_⟩
  rw [← hg₁, ← hd]
  simp only [Units.val_mul, transpose_mul, Matrix.mul_assoc]

end CFSG.RankThree.PartOne.LIT
