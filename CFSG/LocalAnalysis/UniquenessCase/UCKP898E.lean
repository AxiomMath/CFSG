module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUElem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Matrix Subgroup CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj

section Scalar

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {H : Subgroup (GL ι K)}

theorem projH_eq_one_iff_scalar (g : H) :
    projH H g = 1 ↔ ∃ c : Kˣ, GeneralLinearGroup.scalar ι c = (g : GL ι K) := by
  rw [← map_one (projH H), projH_eq_projH_iff, mul_one, inv_mem_iff, mem_subgroupOf]
  exact MonoidHom.mem_range

theorem diag_const_of_projH_eq_one {g : H} {a : ι → K}
    (hg : ((g : GL ι K) : Matrix ι ι K) = diagonal a) (h1 : projH H g = 1) :
    ∃ c : K, c ≠ 0 ∧ ∀ i, a i = c := by
  obtain ⟨c, hc⟩ := (projH_eq_one_iff_scalar g).1 h1
  refine ⟨c, c.ne_zero, fun i => ?_⟩
  have e := Units.ext_iff.1 hc
  rw [GeneralLinearGroup.coe_scalar, scalar_apply, hg] at e
  exact (congrFun (diagonal_injective e) i).symm

theorem projH_eq_one_of_diag_const {g : H} {a : ι → K} {c : K} (hc : c ≠ 0)
    (hg : ((g : GL ι K) : Matrix ι ι K) = diagonal a) (ha : ∀ i, a i = c) : projH H g = 1 := by
  rw [projH_eq_one_iff_scalar]
  refine ⟨Units.mk0 c hc, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, scalar_apply, hg]
  congr 1
  funext i
  exact (ha i).symm

theorem diag_ratio_of_projH_eq {g g' : H} {a a' : ι → K}
    (hg : ((g : GL ι K) : Matrix ι ι K) = diagonal a)
    (hg' : ((g' : GL ι K) : Matrix ι ι K) = diagonal a')
    (hproj : projH H g = projH H g') : ∃ c : K, c ≠ 0 ∧ ∀ i, a' i = a i * c := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 (mem_subgroupOf.1 (projH_eq_projH_iff.1 hproj))
  refine ⟨c, c.ne_zero, fun i => ?_⟩
  have e : (g' : GL ι K) = (g : GL ι K) * GeneralLinearGroup.scalar ι c := by
    rw [hc]
    simp
  have e2 := Units.ext_iff.1 e
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, hg, hg',
    diagonal_mul_diagonal] at e2
  exact congrFun (diagonal_injective e2) i

theorem map_diagonal_apply_fix {φ : K ≃+* K} {a : ι → K} (ha : ∀ i, φ (a i) = a i) (i j : ι) :
    φ (diagonal a i j) = diagonal a i j := by
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, ha]
  · rw [diagonal_apply_ne _ hij, map_zero]

end Scalar

section Elements

variable {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K)

theorem uFieldAut_projH_eq_of_fix {n : ℕ} (hn : 1 ≤ n) {φ : K ≃+* K} {g : StatedSU n (p ^ f) K}
    (hg : ∀ i j, φ (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) :
    uFieldAut h hn φ (projH _ g) = projH _ g := by
  rw [uFieldAut_proj]
  congr 1
  exact Subtype.ext (Units.ext (Matrix.ext hg))

theorem coe_uDiag2_zero_one {ζ : K} (hζ0 : ζ ≠ 0) (hζ : h.norm ζ = 1) :
    (((uDiag2 h (show (0 : Fin 3) ≠ 1 by decide) hζ0 hζ : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal ![ζ, ζ⁻¹, 1] := by
  rw [coe_uDiag2]
  congr 1
  ext k
  fin_cases k <;> simp

theorem coe_uDiag2_zero_two {ζ : K} (hζ0 : ζ ≠ 0) (hζ : h.norm ζ = 1) :
    (((uDiag2 h (show (0 : Fin 3) ≠ 2 by decide) hζ0 hζ : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal ![ζ, 1, ζ⁻¹] := by
  rw [coe_uDiag2]
  congr 1
  ext k
  fin_cases k <;> simp

theorem coe_uDiag2_one_two {ζ : K} (hζ0 : ζ ≠ 0) (hζ : h.norm ζ = 1) :
    (((uDiag2 h (show (1 : Fin 3) ≠ 2 by decide) hζ0 hζ : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal ![1, ζ, ζ⁻¹] := by
  rw [coe_uDiag2]
  congr 1
  ext k
  fin_cases k <;> simp

theorem coe_uDiag2_mul {ζ : K} (hζ0 : ζ ≠ 0) (hζ : h.norm ζ = 1) :
    (((uDiag2 h (show (0 : Fin 3) ≠ 2 by decide) hζ0 hζ *
      uDiag2 h (show (1 : Fin 3) ≠ 2 by decide) hζ0 hζ : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = diagonal ![ζ, ζ, ζ⁻¹ * ζ⁻¹] := by
  rw [Subgroup.coe_mul, Units.val_mul, coe_uDiag2_zero_two, coe_uDiag2_one_two,
    diagonal_mul_diagonal]
  congr 1
  ext k
  fin_cases k <;> simp

theorem coe_uRot_zero_one {ν : ℕ} (h : UnitaryFieldData 2 ν K) :
    (((uRot h (show (0 : Fin 3) ≠ 1 by decide) : StatedSU 3 (2 ^ ν) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  haveI := h.charP
  rw [coe_uRot]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [single_apply, one_apply, CharTwo.neg_eq]

theorem swap_mul_diagonal (a b c : K) :
    (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) * diagonal ![a, b, c] =
      diagonal ![b, a, c] * !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply]

end Elements

section Main

variable {K : Type} [Field K]

theorem diag_fixed_order {ν : ℕ} (h : UnitaryFieldData 2 ν K) {q : ℕ} (hq : q.Prime) {ζ : K}
    (hζ0 : ζ ≠ 0) (hζN : h.norm ζ = 1) (hζq : orderOf ζ = q) :
    orderOf (projH _ (uDiag2 h (show (0 : Fin 3) ≠ 1 by decide) hζ0 hζN)) = q ∧
      ∀ φ : K ≃+* K, φ ζ = ζ →
        uFieldAut h (by norm_num) φ (projH _ (uDiag2 h (show (0 : Fin 3) ≠ 1 by decide) hζ0 hζN)) =
          projH _ (uDiag2 h (show (0 : Fin 3) ≠ 1 by decide) hζ0 hζN) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hζq1 : ζ ^ q = 1 := hζq ▸ pow_orderOf_eq_one ζ
  have hd := coe_uDiag2_zero_one h hζ0 hζN
  generalize uDiag2 h (show (0 : Fin 3) ≠ 1 by decide) hζ0 hζN = d at hd ⊢
  refine ⟨orderOf_eq_prime ?_ ?_, fun φ hφ => ?_⟩
  · rw [← map_pow]
    refine projH_eq_one_of_diag_const (a := ![ζ, ζ⁻¹, 1] ^ q) one_ne_zero ?_ ?_
    · simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hd, diagonal_pow]
    · intro i
      fin_cases i <;> simp [hζq1]
  · intro hy
    obtain ⟨c, -, hc⟩ := diag_const_of_projH_eq_one hd hy
    have h0 : ζ = 1 := by simpa using (hc 0).trans (hc 2).symm
    rw [h0, orderOf_one] at hζq
    exact hq.one_lt.ne hζq
  · apply uFieldAut_projH_eq_of_fix
    rw [hd]
    refine map_diagonal_apply_fix (fun i => ?_)
    fin_cases i <;> simp [hφ]

theorem toral_E9_data {ν : ℕ} (h : UnitaryFieldData 2 ν K) {ζ : K} (hζ0 : ζ ≠ 0)
    (hζN : h.norm ζ = 1) (hζ9 : orderOf ζ = 9) :
    ∃ e f g : StatedProj (StatedSU 3 (2 ^ ν) K), orderOf e = 3 ∧ orderOf f = 3 ∧ e * f = f * e ∧
      f ∉ Subgroup.zpowers e ∧ g * e = e * g ∧ g * f = f⁻¹ * g ∧
      ∀ φ : K ≃+* K, φ ζ = ζ →
        uFieldAut h (by norm_num) φ e = e ∧ uFieldAut h (by norm_num) φ f = f := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hζ9' : ζ ^ 9 = 1 := hζ9 ▸ pow_orderOf_eq_one ζ
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω = ζ ^ 3 := ⟨_, rfl⟩
  have hω0 : ω ≠ 0 := by rw [hω]; exact pow_ne_zero 3 hζ0
  have hωN : h.norm ω = 1 := by
    have : h.norm ω = h.norm ζ ^ 3 := by
      simp only [UnitaryFieldData.norm, hω, map_pow, mul_pow]
    rw [this, hζN, one_pow]
  have hω3 : ω ^ 3 = 1 := by rw [hω, ← pow_mul]; exact hζ9'
  have hω1 : ω ≠ 1 := by
    intro h1
    have h3 : ζ ^ 3 = 1 := by rw [← hω]; exact h1
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hζ9] at this
    omega
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    exact hω1 (by linear_combination hω3 - ω * h2)
  have hζinv : (ζ⁻¹ * ζ⁻¹) ^ 3 = ω := by
    rw [hω]
    field_simp
    linear_combination -hζ9'
  obtain ⟨E, hEdef⟩ : ∃ E : StatedSU 3 (2 ^ ν) K,
      E = uDiag2 h (show (0 : Fin 3) ≠ 2 by decide) hζ0 hζN *
        uDiag2 h (show (1 : Fin 3) ≠ 2 by decide) hζ0 hζN := ⟨_, rfl⟩
  have hEm : ((E : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![ζ, ζ, ζ⁻¹ * ζ⁻¹] := by
    rw [hEdef]
    exact coe_uDiag2_mul h hζ0 hζN
  obtain ⟨F, hFdef⟩ : ∃ F : StatedSU 3 (2 ^ ν) K,
      F = uDiag2 h (show (0 : Fin 3) ≠ 1 by decide) hω0 hωN := ⟨_, rfl⟩
  have hFm : ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![ω, ω⁻¹, 1] := by
    rw [hFdef]
    exact coe_uDiag2_zero_one h hω0 hωN
  obtain ⟨G, hGdef⟩ : ∃ G : StatedSU 3 (2 ^ ν) K,
      G = uRot h (show (0 : Fin 3) ≠ 1 by decide) := ⟨_, rfl⟩
  have hGm : ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
    rw [hGdef]
    exact coe_uRot_zero_one h
  have he3 : orderOf (projH _ E) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      refine projH_eq_one_of_diag_const (a := ![ζ, ζ, ζ⁻¹ * ζ⁻¹] ^ 3) hω0 ?_ ?_
      · simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hEm, diagonal_pow]
      · intro i
        fin_cases i
        · simpa using hω.symm
        · simpa using hω.symm
        · simpa using hζinv
    · intro h1
      obtain ⟨c, -, hc⟩ := diag_const_of_projH_eq_one hEm h1
      have h02 : ζ = ζ⁻¹ * ζ⁻¹ := by simpa using (hc 0).trans (hc 2).symm
      apply hω1
      rw [hω]
      field_simp at h02
      linear_combination h02
  have hf3 : orderOf (projH _ F) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      refine projH_eq_one_of_diag_const (a := ![ω, ω⁻¹, 1] ^ 3) one_ne_zero ?_ ?_
      · simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hFm, diagonal_pow]
      · intro i
        fin_cases i <;> simp [inv_pow, hω3]
    · intro h1
      obtain ⟨c, -, hc⟩ := diag_const_of_projH_eq_one hFm h1
      exact hω1 (by simpa using (hc 0).trans (hc 2).symm)
  have hne : ∀ m : ℕ, projH _ F ≠ projH _ E ^ m := by
    intro m hm
    rw [← map_pow] at hm
    obtain ⟨c, hc0, hc⟩ := diag_ratio_of_projH_eq (a := ![ω, ω⁻¹, 1])
      (a' := ![ζ, ζ, ζ⁻¹ * ζ⁻¹] ^ m) hFm
      (by simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hEm, diagonal_pow]) hm
    have h0 := hc 0
    have h1 := hc 1
    simp only [Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    apply hω2
    have h01 : ω * c = ω⁻¹ * c := h0.symm.trans h1
    have h02 := mul_right_cancel₀ hc0 h01
    field_simp at h02
    linear_combination h02
  refine ⟨projH _ E, projH _ F, projH _ G, he3, hf3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hEm, hFm, diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    obtain ⟨m, hm⟩ : ∃ m : ℕ, projH _ E ^ k = projH _ E ^ m := by
      refine ⟨(k % 3).toNat, ?_⟩
      have h1 := zpow_mod_orderOf (projH _ E) k
      rw [he3] at h1
      have h3 : ((k % 3).toNat : ℤ) = k % ((3 : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (by omega)]
        norm_num
      rw [← zpow_natCast, h3, h1]
    exact hne m (by rw [← hk, hm])
  · rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hEm, hGm]
    exact swap_mul_diagonal ζ ζ (ζ⁻¹ * ζ⁻¹)
  · rw [← map_inv (projH (StatedSU 3 (2 ^ ν) K)), ← map_mul, ← map_mul]
    congr 1
    rw [eq_inv_mul_iff_mul_eq]
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hFm, hGm]
    rw [swap_mul_diagonal, ← Matrix.mul_assoc, diagonal_mul_diagonal]
    have h1 : (diagonal fun i => (![ω, ω⁻¹, 1] : Fin 3 → K) i * (![ω⁻¹, ω, 1] : Fin 3 → K) i) =
        1 := by
      rw [← diagonal_one]
      congr 1
      ext k
      fin_cases k <;> simp [hω0]
    rw [h1, Matrix.one_mul]
  · intro φ hφ
    have hφω : φ ω = ω := by rw [hω, map_pow, hφ]
    constructor
    · apply uFieldAut_projH_eq_of_fix
      rw [hEm]
      refine map_diagonal_apply_fix (fun i => ?_)
      fin_cases i <;> simp [hφ]
    · apply uFieldAut_projH_eq_of_fix
      rw [hFm]
      refine map_diagonal_apply_fix (fun i => ?_)
      fin_cases i <;> simp [hφω]

end Main

end CFSG.LocalAnalysis.UniquenessCase.UCK
