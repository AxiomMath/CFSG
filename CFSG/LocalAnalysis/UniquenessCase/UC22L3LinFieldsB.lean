module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3LinFieldsA
import CFSG.LocalAnalysis.UniquenessCase.UC22L3LinMat
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem exists_smul_of_conjAut_comm [Finite F] {A B : GL (Fin 3) F}
    (h : conjAut 3 F A * conjAut 3 F B = conjAut 3 F B * conjAut 3 F A) :
    ∃ u : F, (A : Matrix (Fin 3) (Fin 3) F) * B = u • ((B : Matrix (Fin 3) (Fin 3) F) * A) := by
  have h1 : conjAut 3 F (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  obtain ⟨u, hu⟩ := (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).1 h1
  refine ⟨u, ?_⟩
  have h2 : A * B = GeneralLinearGroup.scalar (Fin 3) u * (B * A) := by
    rw [← hu]
    group
  have h3 := congrArg Units.val h2
  rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at h3
  rw [h3, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem exists_smul_of_conjAut_inv [Finite F] {A B : GL (Fin 3) F}
    (h : conjAut 3 F A * conjAut 3 F B * (conjAut 3 F A)⁻¹ = (conjAut 3 F B)⁻¹) :
    ∃ u : F, (A : Matrix (Fin 3) (Fin 3) F) * B =
      u • (((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * A) := by
  have h1 : conjAut 3 F (A * B * A⁻¹ * B) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨u, hu⟩ := (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).1 h1
  refine ⟨u, ?_⟩
  have h2 : A * B = GeneralLinearGroup.scalar (Fin 3) u * (B⁻¹ * A) := by
    rw [← hu]
    group
  have h3 := congrArg Units.val h2
  rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at h3
  rw [h3, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem conjAut_comm_e_sq_of_mem {G : GL (Fin 3) F} (hG : G ∈ CenG F) :
    conjAut 3 F G * eA F ^ 2 = eA F ^ 2 * conjAut 3 F G := by
  rw [eA_sq, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hG]

theorem coe_toGL_bSL (B : SL(2, F)) :
    ((SpecialLinearGroup.toGL (bSL B) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![(B : Matrix (Fin 2) (Fin 2) F) 0 0, (B : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
        (B : Matrix (Fin 2) (Fin 2) F) 1 0, (B : Matrix (Fin 2) (Fin 2) F) 1 1, 0; 0, 0, 1] := by
  rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_bSL]

theorem comm_of_comm_KS [Finite F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    {x : MulAut (projectiveSL 3 F)} (hx : x ∈ KS F) (hx1 : x ≠ 1)
    (hxc : Nat.Coprime (orderOf x) (6 * p)) {g : MulAut (projectiveSL 3 F)}
    (hg : g ∈ (conjAut 3 F).range) (hgx : g * x = x * g) : g * eA F ^ 2 = eA F ^ 2 * g := by
  obtain ⟨s, ⟨B, rfl⟩, rfl⟩ := hx
  obtain ⟨G, rfl⟩ := hg
  have hxB : MulAut.conj (blockEmb B) =
      conjAut 3 F (SpecialLinearGroup.toGL (bSL B) : GL (Fin 3) F) := by
    rw [conjAut_toGL_eq]
    rfl
  have hpow : ∀ n : ℕ, B ^ n = 1 → MulAut.conj (blockEmb B) ^ n = 1 := fun n hn => by
    rw [← map_pow, ← map_pow, hn, map_one, map_one]
  have hcop : ∀ n : ℕ, n ∣ 6 * p → MulAut.conj (blockEmb B) ^ n = 1 → False := fun n hn h1 =>
    hx1 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_right hn hxc) (orderOf_dvd_of_pow_eq_one h1)))
  have hdet : (B : Matrix (Fin 2) (Fin 2) F) 0 0 * (B : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (B : Matrix (Fin 2) (Fin 2) F) 0 1 * (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    have := B.2
    rwa [Matrix.det_fin_two] at this
  have ht2 : (B : Matrix (Fin 2) (Fin 2) F) 0 0 + (B : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 2 := by
    intro ht
    have hBp : (B : Matrix (Fin 2) (Fin 2) F) ^ p = 1 :=
      pow_char_eq_one_of_trace _ B.2 (by rw [Matrix.trace_fin_two]; exact ht)
    refine hcop p ⟨6, by ring⟩ (hpow p ?_)
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact hBp
  have ht1 : (B : Matrix (Fin 2) (Fin 2) F) 0 0 + (B : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ -1 := by
    intro ht
    have hB3 : (B : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 :=
      pow_three_eq_one_of_trace _ B.2 (by rw [Matrix.trace_fin_two]; exact ht)
    refine hcop 3 ⟨2 * p, by ring⟩ (hpow 3 ?_)
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact hB3
  rw [hxB] at hgx
  obtain ⟨u, hu⟩ := exists_smul_of_conjAut_comm hgx
  rw [coe_toGL_bSL] at hu
  obtain ⟨h02, h12, h20, h21⟩ := entries_of_comm_block (G.isUnit.map Matrix.detMonoidHom).ne_zero
    hdet ht2 ht1 hu
  exact conjAut_comm_e_sq_of_mem (mem_CenG_of_entries h02 h12 h20 h21)

theorem coe_bG_scalar (a : Fˣ) :
    ((bG (GeneralLinearGroup.scalar (Fin 2) a) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![(a : F), 0, 0; 0, (a : F), 0; 0, 0, 1] := by
  rw [coe_bG, GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bM]

theorem ne_one_of_conjAut_bG_ne_one {a : Fˣ}
    (h : conjAut 3 F (bG (GeneralLinearGroup.scalar (Fin 2) a)) ≠ 1) : (a : F) ≠ 1 := by
  intro ha
  have ha1 : a = 1 := Units.ext ha
  rw [ha1, map_one, map_one, map_one] at h
  exact h rfl

theorem comm_of_comm_ZS [Finite F] (h2 : (2 : F) ≠ 0) {d : MulAut (projectiveSL 3 F)}
    (hd : d ∈ ZS F) (hd1 : d ≠ 1) {g : MulAut (projectiveSL 3 F)}
    (hg : g ∈ (conjAut 3 F).range) (hgd : g * d = d * g) : g * eA F ^ 2 = eA F ^ 2 * g := by
  obtain ⟨a, rfl⟩ := exists_of_mem_ZS h2 hd
  obtain ⟨G, rfl⟩ := hg
  obtain ⟨u, hu⟩ := exists_smul_of_conjAut_comm hgd
  rw [coe_bG_scalar] at hu
  obtain ⟨h02, h12, h20, h21⟩ := entries_of_comm_diag (G.isUnit.map Matrix.detMonoidHom).ne_zero
    a.ne_zero (ne_one_of_conjAut_bG_ne_one hd1) hu
  exact conjAut_comm_e_sq_of_mem (mem_CenG_of_entries h02 h12 h20 h21)

theorem not_inv_ZS [Finite F] (h2 : (2 : F) ≠ 0) {d : MulAut (projectiveSL 3 F)}
    (hd : d ∈ ZS F) (hd1 : d ≠ 1) (hdo : Odd (orderOf d)) {g : MulAut (projectiveSL 3 F)}
    (hg : g ∈ (conjAut 3 F).range) : g * d * g⁻¹ ≠ d⁻¹ := by
  obtain ⟨a, rfl⟩ := exists_of_mem_ZS h2 hd
  obtain ⟨G, rfl⟩ := hg
  intro hinv
  obtain ⟨u, hu⟩ := exists_smul_of_conjAut_inv hinv
  rw [coe_bG_scalar, ← map_inv, ← map_inv, coe_bG_scalar] at hu
  have ha1 := ne_one_of_conjAut_bG_ne_one hd1
  have ha2 : (a : F) * a ≠ 1 := by
    intro h
    have h' : ((a : F) - 1) * ((a : F) + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact ha1 (sub_eq_zero.1 h0)
    ·
      have ham : (a : F) = -1 := eq_neg_of_add_eq_zero_left h0
      have hD : bG (GeneralLinearGroup.scalar (Fin 2) a) = (dG : GL (Fin 3) F) := by
        apply Units.ext
        rw [coe_bG_scalar, ham, coe_dG, coe_dNeg]
      rw [hD, ← eA_sq] at hdo
      have h4 : (eA F ^ 2) ^ 2 = 1 := by
        rw [← pow_mul, eA, ← map_pow, ← map_pow, eSL_pow_four, map_one, map_one]
      have hne : eA F ^ 2 ≠ 1 := by
        rw [eA, ← map_pow, ← map_pow]
        intro h1
        have := conj_injective_Y (h1.trans (map_one _).symm)
        rw [eSL_sq] at this
        exact tInv_ne_one h2 (by rw [tInv, this])
      rw [orderOf_eq_prime h4 hne] at hdo
      exact (Nat.not_odd_iff_even.2 even_two) hdo
  exact false_of_conj_diag_inv (G.isUnit.map Matrix.detMonoidHom).ne_zero
    (show (a : F) * ((a⁻¹ : Fˣ) : F) = 1 by simp) ha2 hu

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin
