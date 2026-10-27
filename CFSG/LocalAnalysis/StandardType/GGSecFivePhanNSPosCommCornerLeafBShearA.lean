module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType

open Matrix

open scoped MatrixGroups

section ShearAlg

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

theorem ggNSPosPF3C_sh_norm_P1_mul_P1 {Q1 : Matrix (Fin n) (Fin n) K}
    (h : Q1 * Q1 = Q1) (Y : Matrix (Fin n) (Fin n) K) : Q1 * (Q1 * Y) = Q1 * Y := by
  rw [← mul_assoc, h]

theorem ggNSPosPF3C_sh_norm_P2_mul_P2 {Q2 : Matrix (Fin n) (Fin n) K}
    (h : Q2 * Q2 = Q2) (Y : Matrix (Fin n) (Fin n) K) : Q2 * (Q2 * Y) = Q2 * Y := by
  rw [← mul_assoc, h]

theorem ggNSPosPF3C_sh_norm_P1_mul_P2 {Q1 Q2 : Matrix (Fin n) (Fin n) K}
    (h : Q1 * Q2 = 0) (Y : Matrix (Fin n) (Fin n) K) : Q1 * (Q2 * Y) = 0 := by
  rw [← mul_assoc, h, zero_mul]

theorem ggNSPosPF3C_sh_norm_P2_mul_P1 {Q1 Q2 : Matrix (Fin n) (Fin n) K}
    (h : Q2 * Q1 = 0) (Y : Matrix (Fin n) (Fin n) K) : Q2 * (Q1 * Y) = 0 := by
  rw [← mul_assoc, h, zero_mul]

theorem ggNSPosPF3C_sh_norm_mul_of_comm {Q D : Matrix (Fin n) (Fin n) K}
    (h : Q * D = D * Q) (Y : Matrix (Fin n) (Fin n) K) : Q * (D * Y) = D * (Q * Y) := by
  rw [← mul_assoc, h, mul_assoc]

theorem ggNSPosPF3C_sh_norm_X_cube {Xm : Matrix (Fin n) (Fin n) K}
    (h : Xm * Xm * Xm = 1) (Y : Matrix (Fin n) (Fin n) K) :
    Xm * (Xm * (Xm * Y)) = Y := by
  rw [← mul_assoc, ← mul_assoc, h, one_mul]

theorem ggNSPosPF3C_sh_norm_Ymul_of_smul {Y X : Matrix (Fin n) (Fin n) K} {ω : K}
    (h : Y * X = ω • (X * Y)) (Z : Matrix (Fin n) (Fin n) K) :
    Y * (X * Z) = ω • (X * (Y * Z)) := by
  rw [← mul_assoc, h, smul_mul_assoc, mul_assoc]

theorem ggNSPosPF3C_sh_mul_P1P2_11 {Q1 Q2 A D : Matrix (Fin n) (Fin n) K}
    (hQ1 : Q1 * Q1 = Q1) (hQ2 : Q2 * Q2 = Q2) (hQ12 : Q1 * Q2 = 0)
    (hQ21 : Q2 * Q1 = 0) (hD1 : Q1 * D = D * Q1) (hD2 : Q2 * D = D * Q2) :
    (A * Q1 + Q2) * (D * Q1 + Q2) = (A * D) * Q1 + Q2 := by
  noncomm_ring [hQ1, hQ2, hQ12, hQ21, hD1, hD2,
    ggNSPosPF3C_sh_norm_P1_mul_P1 hQ1, ggNSPosPF3C_sh_norm_P2_mul_P2 hQ2,
    ggNSPosPF3C_sh_norm_P1_mul_P2 hQ12, ggNSPosPF3C_sh_norm_P2_mul_P1 hQ21,
    ggNSPosPF3C_sh_norm_mul_of_comm hD1, ggNSPosPF3C_sh_norm_mul_of_comm hD2]

theorem ggNSPosPF3C_sh_mul_P1P2_one {Q1 Q2 A C D : Matrix (Fin n) (Fin n) K}
    (hQ1 : Q1 * Q1 = Q1) (hQ2 : Q2 * Q2 = Q2) (hQ12 : Q1 * Q2 = 0)
    (hQ21 : Q2 * Q1 = 0) (hD1 : Q1 * D = D * Q1) (hD2 : Q2 * D = D * Q2) :
    (A * Q1 + C * Q2) * (D * Q1 + Q2) = (A * D) * Q1 + C * Q2 := by
  noncomm_ring [hQ1, hQ2, hQ12, hQ21, hD1, hD2,
    ggNSPosPF3C_sh_norm_P1_mul_P1 hQ1, ggNSPosPF3C_sh_norm_P2_mul_P2 hQ2,
    ggNSPosPF3C_sh_norm_P1_mul_P2 hQ12, ggNSPosPF3C_sh_norm_P2_mul_P1 hQ21,
    ggNSPosPF3C_sh_norm_mul_of_comm hD1, ggNSPosPF3C_sh_norm_mul_of_comm hD2]

theorem ggNSPosPF3C_sh_mul_right_comm {Q1 Q2 A C L : Matrix (Fin n) (Fin n) K}
    (hQ1 : Q1 * Q1 = Q1) (hQ2 : Q2 * Q2 = Q2)
    (hL1 : Q1 * L = L * Q1) (hL2 : Q2 * L = L * Q2) :
    (A * Q1 + C * Q2) * L = (A * L) * Q1 + (C * L) * Q2 := by
  noncomm_ring [hQ1, hQ2, hL1, hL2,
    ggNSPosPF3C_sh_norm_P1_mul_P1 hQ1, ggNSPosPF3C_sh_norm_P2_mul_P2 hQ2,
    ggNSPosPF3C_sh_norm_mul_of_comm hL1, ggNSPosPF3C_sh_norm_mul_of_comm hL2]

theorem ggNSPosPF3C_sh_sq_commute {Q Xm : Matrix (Fin n) (Fin n) K}
    (h : Q * Xm = Xm * Q) : Q * (Xm * Xm) = (Xm * Xm) * Q := by
  calc Q * (Xm * Xm) = (Q * Xm) * Xm := by rw [← mul_assoc]
    _ = (Xm * Q) * Xm := by rw [h]
    _ = Xm * (Q * Xm) := by rw [mul_assoc]
    _ = Xm * (Xm * Q) := by rw [h]
    _ = (Xm * Xm) * Q := by rw [← mul_assoc]

theorem ggNSPosPF3C_sh_X_inv_mat (X : GL (Fin n) K)
    (hX3 : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) *
        (X : Matrix (Fin n) (Fin n) K) = 1) :
    ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) := by
  have hGL : X * (X * X) = 1 := by
    apply Units.ext
    simpa only [Units.val_mul, Units.val_one, mul_assoc] using hX3
  have h2 : X * X = X⁻¹ := eq_inv_of_mul_eq_one_right hGL
  rw [← h2, Units.val_mul]

theorem ggNSPosPF3C_sh_TS {Xm : Matrix (Fin n) (Fin n) K} {ω : K}
    (hX3 : Xm * Xm * Xm = 1) (hω : ω ^ 2 + ω + 1 = 0) :
    (1 + ω ^ 2 • Xm + Xm * Xm) * (1 + Xm + ω • (Xm * Xm)) = 1 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hX3a : Xm * (Xm * Xm) = 1 := by rw [← mul_assoc]; exact hX3
  have hexp : (1 + ω ^ 2 • Xm + Xm * Xm) * (1 + Xm + ω • (Xm * Xm)) =
      (1 + ω ^ 3 + 1) • (1 : Matrix (Fin n) (Fin n) K) + (1 + ω ^ 2 + ω) • Xm +
        (ω + ω ^ 2 + 1) • (Xm * Xm) := by
    simp only [mul_add, add_mul, mul_assoc, mul_one, one_mul, smul_mul_assoc, mul_smul_comm,
      smul_smul, smul_add, one_smul, hX3a, pow_two]
    module
  rw [hexp]
  have hc : (1 : K) + ω ^ 3 + 1 = 1 := by linear_combination hω3 + h2
  have ha : (1 : K) + ω ^ 2 + ω = 0 := by linear_combination hω
  have hb : ω + ω ^ 2 + 1 = 0 := by linear_combination hω
  rw [hc, ha, hb, zero_smul, zero_smul, add_zero, add_zero, one_smul]

theorem ggNSPosPF3C_sh_YT {Xm Ym : Matrix (Fin n) (Fin n) K} {ω : K}
    (hX3 : Xm * Xm * Xm = 1) (hω3 : ω ^ 3 = 1) (hYX : Ym * Xm = ω • (Xm * Ym)) :
    Ym * (1 + ω ^ 2 • Xm + Xm * Xm) =
      (Xm * (1 + ω ^ 2 • Xm + Xm * Xm)) * Ym := by
  have hω3' : ω * (ω * ω) = 1 := by rw [← mul_assoc]; simpa [pow_succ, pow_two] using hω3
  noncomm_ring [hYX, ggNSPosPF3C_sh_norm_Ymul_of_smul hYX, hX3, hω3',
    ggNSPosPF3C_sh_norm_X_cube hX3, smul_smul, one_smul, mul_smul_comm, smul_mul_assoc]

theorem ggNSPosPF3C_sh_conj_eq {Q1 Q2 Xm lm li : Matrix (Fin n) (Fin n) K} {ζ : K}
    (hQ1 : Q1 * Q1 = Q1) (hQ2 : Q2 * Q2 = Q2) (hQ12 : Q1 * Q2 = 0) (hQ21 : Q2 * Q1 = 0)
    (hX1 : Q1 * Xm = Xm * Q1) (hX2 : Q2 * Xm = Xm * Q2)
    (hXi1 : Q1 * (Xm * Xm) = (Xm * Xm) * Q1) (hXi2 : Q2 * (Xm * Xm) = (Xm * Xm) * Q2)
    (hl1 : Q1 * lm = lm * Q1) (hl2 : Q2 * lm = lm * Q2)
    (hli1 : Q1 * li = li * Q1) (hli2 : Q2 * li = li * Q2)
    (hlX2 : lm * (Xm * Xm) = ζ ^ 2 • ((Xm * Xm) * lm))
    (hlinv : lm * li = 1) (hX3 : Xm * Xm * Xm = 1) :
    (Xm * Q1 + Q2) * lm * (Xm * Xm * Q1 + Q2) * li = ζ ^ 2 • Q1 + Q2 := by
  have hstep1 : (Xm * Q1 + Q2) * lm = (Xm * lm) * Q1 + lm * Q2 := by
    simpa only [one_mul] using ggNSPosPF3C_sh_mul_right_comm (C := 1) hQ1 hQ2 hl1 hl2
  have hstep2 : ((Xm * lm) * Q1 + lm * Q2) * (Xm * Xm * Q1 + Q2) =
      ((Xm * lm) * (Xm * Xm)) * Q1 + lm * Q2 :=
    ggNSPosPF3C_sh_mul_P1P2_one hQ1 hQ2 hQ12 hQ21 hXi1 hXi2
  have hstep3 : (Xm * lm) * (Xm * Xm) = ζ ^ 2 • lm := by
    calc (Xm * lm) * (Xm * Xm) = Xm * (lm * (Xm * Xm)) := by rw [mul_assoc]
      _ = Xm * (ζ ^ 2 • ((Xm * Xm) * lm)) := by rw [hlX2]
      _ = ζ ^ 2 • (Xm * ((Xm * Xm) * lm)) := by rw [mul_smul_comm]
      _ = ζ ^ 2 • ((Xm * (Xm * Xm)) * lm) := by rw [← mul_assoc]
      _ = ζ ^ 2 • ((Xm * Xm * Xm) * lm) := by rw [← mul_assoc]
      _ = ζ ^ 2 • (1 * lm) := by rw [hX3]
      _ = ζ ^ 2 • lm := by rw [one_mul]
  calc (Xm * Q1 + Q2) * lm * (Xm * Xm * Q1 + Q2) * li
      = (((Xm * lm) * Q1 + lm * Q2) * (Xm * Xm * Q1 + Q2)) * li := by rw [hstep1]
    _ = (((Xm * lm) * (Xm * Xm)) * Q1 + lm * Q2) * li := by rw [hstep2]
    _ = ((ζ ^ 2 • lm) * Q1 + lm * Q2) * li := by rw [hstep3]
    _ = (ζ ^ 2 • (lm * Q1) + lm * Q2) * li := by rw [smul_mul_assoc]
    _ = (ζ ^ 2 • (Q1 * lm) + lm * Q2) * li := by rw [← hl1]
    _ = (ζ ^ 2 • (Q1 * lm)) * li + (lm * Q2) * li := by rw [add_mul]
    _ = ζ ^ 2 • ((Q1 * lm) * li) + (lm * Q2) * li := by rw [smul_mul_assoc]
    _ = ζ ^ 2 • (Q1 * (lm * li)) + (lm * Q2) * li := by rw [mul_assoc]
    _ = ζ ^ 2 • (Q1 * 1) + (lm * Q2) * li := by rw [hlinv]
    _ = ζ ^ 2 • Q1 + (lm * Q2) * li := by rw [mul_one]
    _ = ζ ^ 2 • Q1 + lm * (Q2 * li) := by rw [mul_assoc]
    _ = ζ ^ 2 • Q1 + lm * (li * Q2) := by rw [hli2]
    _ = ζ ^ 2 • Q1 + (lm * li) * Q2 := by rw [mul_assoc]
    _ = ζ ^ 2 • Q1 + 1 * Q2 := by rw [hlinv]
    _ = ζ ^ 2 • Q1 + Q2 := by rw [one_mul]

theorem ggNSPosPF3C_sh_cube_root_cases {ω ζ : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hζ : ζ ^ 3 = 1) : ∃ j : ℕ, ζ = ω ^ j := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hfac : (ζ - 1) * (ζ - ω) * (ζ - ω ^ 2) = ζ ^ 3 - 1 := by
    linear_combination (ζ - ζ ^ 2) * hω + (ζ - 1) * hω3
  have hz : (ζ - 1) * (ζ - ω) * (ζ - ω ^ 2) = 0 := by rw [hfac, hζ, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · rcases mul_eq_zero.mp h with h1 | h2
    · exact ⟨0, by rw [pow_zero]; linear_combination h1⟩
    · exact ⟨1, by rw [pow_one]; linear_combination h2⟩
  · exact ⟨2, by linear_combination h⟩

theorem ggNSPosPF3C_sh_omega_ne_zero {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  intro h
  rw [h] at hω
  norm_num at hω

end ShearAlg

end CFSG.StandardType

end
