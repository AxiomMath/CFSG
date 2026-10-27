module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.CharP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem mul_fin_two_apply (A B : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem pgl_mk_eq_one_iff {M : GL (Fin 2) F} :
    Matrix.ProjGenLinGroup.mk M = 1 ↔ ∃ c : F, (M : Matrix (Fin 2) (Fin 2) F) = c • 1 := by
  rw [Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, by rw [GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]; rfl⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := M.isUnit
      rw [hc, zero_smul] at this
      exact not_isUnit_zero this
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, hc, Matrix.smul_one_eq_diagonal]
    rfl

theorem pgl_mk_comm_iff {M N : GL (Fin 2) F} :
    Matrix.ProjGenLinGroup.mk M * Matrix.ProjGenLinGroup.mk N =
        Matrix.ProjGenLinGroup.mk N * Matrix.ProjGenLinGroup.mk M ↔
      ∃ c : F, (M : Matrix (Fin 2) (Fin 2) F) * N = c • ((N : Matrix (Fin 2) (Fin 2) F) * M) := by
  rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, pgl_mk_eq_one_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h : (M : Matrix (Fin 2) (Fin 2) F) * N =
        ((M * N * (N * M)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (N * M : GL (Fin 2) F) := by
      rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
    rw [h, hc, smul_mul_assoc, one_mul, Units.val_mul]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [Units.val_mul, Units.val_mul, hc, smul_mul_assoc, ← Units.val_mul N M, Units.mul_inv]

theorem sq_scalar_of_comm {G : Matrix (Fin 2) (Fin 2) F} (h2 : (2 : F) ≠ 0) {c d : F} (hE : G * !![0, -1; 1, 0] = c • (!![0, -1; 1, 0] * G))
    (hR : G * !![1, 0; 0, -1] = d • (!![1, 0; 0, -1] * G)) :
    ∃ s : F, G * G = s • 1 := by
  have e00 := congrFun (congrFun hE 0) 0
  have e01 := congrFun (congrFun hE 0) 1
  have e10 := congrFun (congrFun hE 1) 0
  have e11 := congrFun (congrFun hE 1) 1
  have r00 := congrFun (congrFun hR 0) 0
  have r01 := congrFun (congrFun hR 0) 1
  have r10 := congrFun (congrFun hR 1) 0
  have r11 := congrFun (congrFun hR 1) 1
  simp only [mul_fin_two_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one] at e00 e01 e10 e11 r00 r01 r10 r11
  refine ⟨G 0 0 * G 0 0 + G 0 1 * G 1 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul_fin_two_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> grind

theorem pgl_sq_eq_one_of_comm (h2 : (2 : F) ≠ 0) {ME MR : GL (Fin 2) F}
    (hME : (ME : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0])
    (hMR : (MR : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, -1]) (g : PGL(Fin 2, F))
    (h1 : g * Matrix.ProjGenLinGroup.mk ME = Matrix.ProjGenLinGroup.mk ME * g)
    (h2' : g * Matrix.ProjGenLinGroup.mk MR = Matrix.ProjGenLinGroup.mk MR * g) : g ^ 2 = 1 := by
  obtain ⟨G, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  obtain ⟨c, hc⟩ := pgl_mk_comm_iff.1 h1
  obtain ⟨d, hd⟩ := pgl_mk_comm_iff.1 h2'
  rw [hME] at hc
  rw [hMR] at hd
  obtain ⟨s, hs⟩ := sq_scalar_of_comm h2 hc hd
  rw [← map_pow, pgl_mk_eq_one_iff]
  exact ⟨s, by rw [Units.val_pow_eq_pow_val, sq, hs]⟩

theorem eq_scalar_of_comm_conj {p : ℕ} [hp : Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    {M : Matrix (Fin 2) (Fin 2) F}
    (hE : M * (!![0, -1; 1, 0] * M * !![0, 1; -1, 0]) =
      (!![0, -1; 1, 0] * M * !![0, 1; -1, 0]) * M)
    (hR : M * (!![1, 0; 0, -1] * M * !![1, 0; 0, -1]) =
      (!![1, 0; 0, -1] * M * !![1, 0; 0, -1]) * M)
    {s : F} (hs : M ^ p = s • 1) : ∃ c : F, M = c • 1 := by
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1
      ((CharP.cast_eq_zero_iff F p 2).1 h'))
  have e01 := congrFun (congrFun hE 0) 1
  have e10 := congrFun (congrFun hE 1) 0
  have e00 := congrFun (congrFun hE 0) 0
  have e11 := congrFun (congrFun hE 1) 1
  have r01 := congrFun (congrFun hR 0) 1
  have r10 := congrFun (congrFun hR 1) 0
  simp only [mul_fin_two_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e01 e10 e00 e11 r01 r10
  have hb : M 0 1 * (M 0 0 - M 1 1) = 0 := by grind
  have hc : M 1 0 * (M 0 0 - M 1 1) = 0 := by grind
  have hbc : M 0 1 ^ 2 = M 1 0 ^ 2 := by grind
  have hM : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := Matrix.eta_fin_two M
  by_cases had : M 0 0 = M 1 1
  ·
    obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two hp2
    have hε : M 1 0 = M 0 1 ∨ M 1 0 = -M 0 1 := by
      exact sq_eq_sq_iff_eq_or_eq_neg.1 hbc.symm
    obtain ⟨ε, hε1, hεM⟩ : ∃ ε : F, ε ^ 2 = 1 ∧ M 1 0 = ε * M 0 1 := by
      rcases hε with h | h
      · exact ⟨1, one_pow 2, by rw [h, one_mul]⟩
      · exact ⟨-1, by norm_num, by rw [h, neg_one_mul]⟩
    set N : Matrix (Fin 2) (Fin 2) F := !![0, 1; ε, 0] with hNdef
    have hN2 : N * N = ε • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hNdef, mul_fin_two_apply]
    have hNp : N ^ p = ε ^ m • N := by
      rw [hm, pow_succ, pow_mul, sq, hN2, smul_pow, one_pow, smul_mul_assoc, one_mul]
    have hMN : M = M 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) + M 0 1 • N := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hNdef, had, hεM, mul_comm]
    have hcomm : Commute (M 0 0 • (1 : Matrix (Fin 2) (Fin 2) F)) (M 0 1 • N) :=
      ((Commute.one_left N).smul_left _).smul_right _
    have hpow : M ^ p = M 0 0 ^ p • (1 : Matrix (Fin 2) (Fin 2) F) + (M 0 1 ^ p * ε ^ m) • N := by
      conv_lhs => rw [hMN]
      rw [add_pow_char_of_commute p hcomm, smul_pow, one_pow, smul_pow, hNp, smul_smul]
    have h01 := congrFun (congrFun (hpow.symm.trans hs) 0) 1
    simp [hNdef] at h01
    have hb0 : M 0 1 = 0 := by
      rcases h01 with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · rw [h] at hε1
        simp at hε1
    refine ⟨M 0 0, ?_⟩
    conv_lhs => rw [hMN]
    rw [hb0, zero_smul, add_zero]
  ·
    have hb0 : M 0 1 = 0 := by
      rcases mul_eq_zero.1 hb with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) had
    have hc0 : M 1 0 = 0 := by
      rcases mul_eq_zero.1 hc with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) had
    have hdiag : M = Matrix.diagonal ![M 0 0, M 1 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb0, hc0]
    have hpow := hs
    rw [hdiag, Matrix.diagonal_pow] at hpow
    have h00 := congrFun (congrFun hpow 0) 0
    have h11 := congrFun (congrFun hpow 1) 1
    simp at h00 h11
    exact absurd (frobenius_inj F p (by
      simp only [frobenius_def]
      rw [h00, h11])) had

theorem card_pgl_two_mul [Fintype F] :
    Nat.card PGL(Fin 2, F) * (Fintype.card F - 1) =
      (Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 2 - Fintype.card F) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (GL (Fin 2) F))
  have hinj : Function.Injective (GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) := by
    intro u v h
    have h' := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h'
    exact Units.ext h'
  have hc : Nat.card (Subgroup.center (GL (Fin 2) F)) = Fintype.card F - 1 := by
    rw [GeneralLinearGroup.center_eq_range_scalar,
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units,
      Nat.card_eq_fintype_card]
  rw [Matrix.card_GL_field, hc, Fin.prod_univ_two] at h1
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h1
  exact h1.symm

theorem eight_dvd_card_pgl_two [Fintype F] (hq : Odd (Fintype.card F)) :
    8 ∣ Nat.card PGL(Fin 2, F) := by
  have h := card_pgl_two_mul (F := F)
  obtain ⟨t, ht⟩ := hq
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.card_pos (α := F)
    have h2 : 2 ≤ Fintype.card F := by
      by_contra h3
      have : Fintype.card F = 1 := by omega
      exact absurd (Fintype.card_le_one_iff_subsingleton.1 this.le) (not_subsingleton F)
    omega
  have hcard : Nat.card PGL(Fin 2, F) = (Fintype.card F ^ 2 - 1) * Fintype.card F := by
    have e : (Fintype.card F ^ 2 - Fintype.card F) =
        Fintype.card F * (Fintype.card F - 1) := by
      rw [Nat.mul_sub, mul_one, sq]
    rw [e, ← mul_assoc] at h
    exact Nat.eq_of_mul_eq_mul_right hq1 h
  rw [hcard, ht]
  obtain ⟨u, hu⟩ := Nat.even_mul_succ_self t
  refine Dvd.dvd.mul_right ?_ _
  have e : (2 * t + 1) ^ 2 - 1 = 4 * (t * (t + 1)) := by
    have : (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 := by ring
    omega
  rw [e, hu]
  exact ⟨u, by ring⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin
