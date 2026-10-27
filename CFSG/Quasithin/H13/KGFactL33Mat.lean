module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13.A5.KGL33

open Matrix

variable (F : Type) [Field F]

@[expose] def tMat : Matrix (Fin 3) (Fin 3) F := !![1, 1, 0; -1, 1, 0; 0, 0, -1]

@[expose] def wMat : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 1, 0, 0; 0, 0, -1]

@[expose] def rMat : Matrix (Fin 3) (Fin 3) F := !![0, -1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def dMat : Matrix (Fin 3) (Fin 3) F := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

variable {F}

theorem rMat_mul_rMat : rMat F * rMat F = dMat F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rMat, dMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem dMat_mul_dMat : dMat F * dMat F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem wMat_mul_wMat : wMat F * wMat F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem wMat_mul_tMat_mul_wMat : wMat F * tMat F * wMat F = rMat F * tMat F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, tMat, rMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_wMat : (wMat F).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [wMat]

theorem det_rMat : (rMat F).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [rMat]

theorem det_dMat : (dMat F).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [dMat]

@[expose] def wSL : SpecialLinearGroup (Fin 3) F := ⟨wMat F, det_wMat⟩

@[expose] def rSL : SpecialLinearGroup (Fin 3) F := ⟨rMat F, det_rMat⟩

@[expose] def dSL : SpecialLinearGroup (Fin 3) F := ⟨dMat F, det_dMat⟩

theorem rSL_sq : (rSL : SpecialLinearGroup (Fin 3) F) * rSL = dSL :=
  Subtype.ext rMat_mul_rMat

theorem dSL_sq : (dSL : SpecialLinearGroup (Fin 3) F) * dSL = 1 :=
  Subtype.ext dMat_mul_dMat

theorem wSL_sq : (wSL : SpecialLinearGroup (Fin 3) F) * wSL = 1 :=
  Subtype.ext wMat_mul_wMat

section CharThree

variable [CharP F 3]

theorem three_eq_zero : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3

theorem two_ne_zero' : (2 : F) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F 3] at h1
  omega

theorem eq_zero_of_eq_neg' {x : F} (h : x = -x) : x = 0 := by
  have h2 : (2 : F) * x = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 two_ne_zero'
  · exact h3

theorem tMat_mul_tMat : tMat F * tMat F = rMat F := by
  have h3 := (three_eq_zero : (3 : F) = 0)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tMat, rMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
    | linear_combination h3
    | linear_combination -h3

theorem det_tMat : (tMat F).det = 1 := by
  have h3 := (three_eq_zero : (3 : F) = 0)
  rw [Matrix.det_fin_three]
  simp [tMat]
  linear_combination -h3

@[expose] def tSL : SpecialLinearGroup (Fin 3) F := ⟨tMat F, det_tMat⟩

theorem tSL_sq : (tSL : SpecialLinearGroup (Fin 3) F) * tSL = rSL :=
  Subtype.ext tMat_mul_tMat

theorem wSL_conj : (wSL : SpecialLinearGroup (Fin 3) F) * tSL * wSL⁻¹ = tSL ^ 3 := by
  have hw : (wSL : SpecialLinearGroup (Fin 3) F)⁻¹ = wSL := inv_eq_of_mul_eq_one_right wSL_sq
  rw [hw, pow_succ, pow_two, tSL_sq]
  exact Subtype.ext wMat_mul_tMat_mul_wMat

theorem tSL_pow_eight : (tSL : SpecialLinearGroup (Fin 3) F) ^ 8 = 1 := by
  rw [show (8 : ℕ) = 2 * 2 * 2 from rfl, pow_mul, pow_mul, sq tSL, tSL_sq, sq rSL, rSL_sq,
    sq dSL, dSL_sq]

theorem isPGroup_closure_tSL_wSL :
    IsPGroup 2 (Subgroup.closure {(tSL : SpecialLinearGroup (Fin 3) F), wSL}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht : IsPGroup 2 (Subgroup.zpowers (tSL : SpecialLinearGroup (Fin 3) F)) := by
    have hdvd : orderOf (tSL : SpecialLinearGroup (Fin 3) F) ∣ 2 ^ 3 :=
      orderOf_dvd_of_pow_eq_one tSL_pow_eight
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hw : IsPGroup 2 (Subgroup.zpowers (wSL : SpecialLinearGroup (Fin 3) F)) := by
    have hdvd : orderOf (wSL : SpecialLinearGroup (Fin 3) F) ∣ 2 ^ 1 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact wSL_sq)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hwinv : (wSL : SpecialLinearGroup (Fin 3) F)⁻¹ = wSL := inv_eq_of_mul_eq_one_right wSL_sq
  have hconj : ∀ h ∈ Subgroup.zpowers (tSL : SpecialLinearGroup (Fin 3) F),
      wSL * h * wSL⁻¹ ∈ Subgroup.zpowers (tSL : SpecialLinearGroup (Fin 3) F) := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [← conj_zpow, wSL_conj, ← zpow_natCast, ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers _ _
  have hle : Subgroup.zpowers (wSL : SpecialLinearGroup (Fin 3) F) ≤
      Subgroup.normalizer (Subgroup.zpowers (tSL : SpecialLinearGroup (Fin 3) F) :
        Set (SpecialLinearGroup (Fin 3) F)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconj h, fun hh => ?_⟩
    have := hconj _ hh
    rwa [hwinv, show wSL * (wSL * h * wSL) * wSL = (wSL * wSL) * h * (wSL * wSL) by group,
      wSL_sq, one_mul, mul_one] at this
  refine (IsPGroup.to_sup_of_normal_left' ht hw hle).to_le ?_
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

variable [Fintype F]

theorem eq_one_or_eq_dSL_of_commute (hF : Fintype.card F = 3) (g : SpecialLinearGroup (Fin 3) F)
    (hgt : g * tSL = tSL * g) (hgw : g * wSL = wSL * g) : g = 1 ∨ g = dSL := by
  set M : Matrix (Fin 3) (Fin 3) F := (g : Matrix (Fin 3) (Fin 3) F) with hM
  have hT : M * tMat F = tMat F * M := congrArg Subtype.val hgt
  have hW : M * wMat F = wMat F * M := congrArg Subtype.val hgw
  have hdet : M.det = 1 := g.2
  have hD : M * dMat F = dMat F * M := by
    have c1 : Commute M (tMat F) := hT
    have c2 : Commute M (rMat F) := by rw [← tMat_mul_tMat]; exact c1.mul_right c1
    have c3 : Commute M (dMat F) := by rw [← rMat_mul_rMat]; exact c2.mul_right c2
    exact c3
  have entry : ∀ {A B : Matrix (Fin 3) (Fin 3) F}, A = B → ∀ i j, A i j = B i j :=
    fun h i j => by rw [h]
  have h02 : M 0 2 = 0 := by
    have := entry hD 0 2
    simp [dMat, Matrix.mul_apply, Fin.sum_univ_three] at this
    exact eq_zero_of_eq_neg' this
  have h12 : M 1 2 = 0 := by
    have := entry hD 1 2
    simp [dMat, Matrix.mul_apply, Fin.sum_univ_three] at this
    exact eq_zero_of_eq_neg' this
  have h20 : M 2 0 = 0 := by
    have := entry hD 2 0
    simp [dMat, Matrix.mul_apply, Fin.sum_univ_three] at this
    exact eq_zero_of_eq_neg' this.symm
  have h21 : M 2 1 = 0 := by
    have := entry hD 2 1
    simp [dMat, Matrix.mul_apply, Fin.sum_univ_three] at this
    exact eq_zero_of_eq_neg' this.symm
  have ht00 := entry hT 0 0
  have ht01 := entry hT 0 1
  have hw00 := entry hW 0 0
  simp [tMat, wMat, Matrix.mul_apply, Fin.sum_univ_three, h02, h20, h21] at ht00 ht01 hw00
  have h01 : M 0 1 = 0 := eq_zero_of_eq_neg' (by linear_combination hw00 - ht00)
  have h10 : M 1 0 = 0 := by rw [← hw00, h01]
  have h11 : M 1 1 = M 0 0 := by linear_combination -ht01
  rw [Matrix.det_fin_three, h01, h02, h10, h12, h20, h21, h11] at hdet
  simp only [mul_zero, zero_mul, sub_zero, add_zero] at hdet
  have hp0 : M 0 0 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  have hp2 : M 0 0 * M 0 0 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (M 0 0) hp0
    rw [hF] at this
    simpa [pow_two] using this
  have hc : M 2 2 = 1 := by rw [hp2, one_mul] at hdet; exact hdet
  rcases mul_self_eq_one_iff.1 hp2 with hp | hp
  · left
    apply Subtype.ext
    show M = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, h01, h02, h10, h11, h12, h20, h21, hc]
  · right
    apply Subtype.ext
    show M = dMat F
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dMat, hp, h01, h02, h10, h11, h12, h20, h21, hc]

omit [CharP F 3] in
theorem center_SL_eq_bot (hF : Fintype.card F = 3) :
    Subgroup.center (SpecialLinearGroup (Fin 3) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hrA⟩ := hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have := FiniteField.pow_card r
    rw [hF, hr] at this
    exact this.symm
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

end CharThree

end CFSG.Quasithin.H13.A5.KGL33
