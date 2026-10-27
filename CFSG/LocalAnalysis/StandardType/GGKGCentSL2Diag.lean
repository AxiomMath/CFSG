module

public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
import Mathlib.Algebra.CharP.Two

public section

namespace CFSG.StandardType.KGCentSL2

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def dconj (ν : Fˣ) (A : SL(2, F)) : SL(2, F) :=
  ⟨!![A 0 0, (ν : F) * A 0 1; ((ν⁻¹ : Fˣ) : F) * A 1 0, A 1 1], by
    have h := A.2
    rw [det_fin_two] at h
    rw [det_fin_two_of]
    have hν : (ν : F) * ((ν⁻¹ : Fˣ) : F) = 1 := by simp
    linear_combination h - (A 0 1 * A 1 0) * hν⟩

@[simp] theorem dconj_apply (ν : Fˣ) (A : SL(2, F)) (i j : Fin 2) :
    dconj ν A i j = !![A 0 0, (ν : F) * A 0 1; ((ν⁻¹ : Fˣ) : F) * A 1 0, A 1 1] i j :=
  rfl

theorem dconj_upper (ν : Fˣ) (c : F) : dconj ν (sl2Upper F c) = sl2Upper F ((ν : F) * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem dconj_lower (ν : Fˣ) (c : F) :
    dconj ν (sl2Lower F c) = sl2Lower F (((ν⁻¹ : Fˣ) : F) * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp


section CharTwo

variable [CharP F 2]

omit [CharP F 2] in
private theorem sl2Upper_one_ne_one : sl2Upper F 1 ≠ 1 := by
  intro h
  have := congrArg (fun M : SL(2, F) => M 0 1) h
  simp at this

theorem eq_upper_or_lower {x : SL(2, F)} (hx : x * x = 1) {ν : Fˣ} (hν : (ν : F) ≠ 1)
    (hc : x * dconj ν x = dconj ν x * x) :
    x = sl2Upper F (x 0 1) ∨ x = sl2Lower F (x 1 0) := by
  have e := fun i j => congrArg (fun M : SL(2, F) => M i j) hx
  have f := fun i j => congrArg (fun M : SL(2, F) => M i j) hc
  have e00 := e 0 0
  have e11 := e 1 1
  have f00 := f 0 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11 f00
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hνν : (ν : F) - (ν : F)⁻¹ ≠ 0 := by
    intro h0
    apply hν
    have h1 : (ν : F) * (ν : F) = 1 := by
      have : (ν : F) = (ν : F)⁻¹ := sub_eq_zero.mp h0
      calc (ν : F) * (ν : F) = (ν : F) * (ν : F)⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel₀ ν.ne_zero
    apply CharTwo.sq_injective
    show (ν : F) ^ 2 = 1 ^ 2
    rw [sq, h1, one_pow]
  have hbc : x 0 1 * x 1 0 = 0 := by
    have h3 : x 0 1 * x 1 0 * ((ν : F) - (ν : F)⁻¹) = 0 := by linear_combination -f00
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hνν
  have ha : x 0 0 = 1 := by
    apply CharTwo.sq_injective
    show x 0 0 ^ 2 = 1 ^ 2
    linear_combination e00 - hbc
  have hd : x 1 1 = 1 := by
    apply CharTwo.sq_injective
    show x 1 1 ^ 2 = 1 ^ 2
    linear_combination e11 - hbc
  rcases mul_eq_zero.mp hbc with hb | hc0
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hd, hb]
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hd, hc0]

theorem exists_good [Finite F] (hF : 4 < Nat.card F) :
    ∃ c : F, c ≠ 0 ∧ c ≠ 1 ∧ c ^ 2 + c + 1 ≠ 0 := by
  classical
  by_contra hne
  push Not at hne
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let : Fintype F := Fintype.ofFinite F
  have hcard : Nat.card F ≤ 4 := by
    rw [Nat.card_eq_fintype_card]
    by_cases hr : ∃ r : F, r ^ 2 + r + 1 = 0
    · obtain ⟨r, hr⟩ := hr
      have hsub : (Finset.univ : Finset F) ⊆ {0, 1, r, r + 1} := by
        intro c _
        by_cases h0 : c = 0
        · simp [h0]
        by_cases h1 : c = 1
        · simp [h1]
        have hc := hne c h0 h1
        have hprod : (c + r) * (c + r + 1) = 0 := by linear_combination hc + hr + h2 * (c * r - 1)
        rcases mul_eq_zero.mp hprod with h | h
        · have : c = r := by linear_combination h - h2 * r
          simp [this]
        · have : c = r + 1 := by linear_combination h - h2 * (r + 1)
          simp [this]
      calc Fintype.card F = (Finset.univ : Finset F).card := rfl
        _ ≤ ({0, 1, r, r + 1} : Finset F).card := Finset.card_le_card hsub
        _ ≤ 4 := Finset.card_le_four
    · push Not at hr
      have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
        intro c _
        by_cases h0 : c = 0
        · simp [h0]
        by_cases h1 : c = 1
        · simp [h1]
        exact absurd (hne c h0 h1) (hr c)
      calc Fintype.card F = (Finset.univ : Finset F).card := rfl
        _ ≤ ({0, 1} : Finset F).card := Finset.card_le_card hsub
        _ ≤ 4 := (Finset.card_le_two).trans (by norm_num)
  omega

omit [CharP F 2] in
private theorem upper_eq_dconj {c : F} (hc : c ≠ 0) :
    sl2Upper F c = dconj (Units.mk0 c hc) (sl2Upper F 1) := by
  rw [dconj_upper, Units.val_mk0, mul_one]

omit [CharP F 2] in
private theorem lower_eq_dconj {c : F} (hc : c ≠ 0) :
    sl2Lower F c = dconj (Units.mk0 c hc)⁻¹ (sl2Lower F 1) := by
  rw [dconj_lower, inv_inv, Units.val_mk0, mul_one]

private theorem upper_mul_lower_pow_three : (sl2Upper F 1 * sl2Lower F 1) ^ 3 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
      | linear_combination (2 : F) * h2
      | linear_combination (4 : F) * h2
      | linear_combination (6 : F) * h2

omit [CharP F 2] in
private theorem upper_mul_lower_pow_three_zero_one (κ κ' : F) :
    ((sl2Upper F κ * sl2Lower F κ') ^ 3) 0 1 = κ * (1 + κ * κ') ^ 2 + 2 * (κ + κ ^ 2 * κ') := by
  simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem eq_one_of_commute_dconj [Finite F] (hF : 4 < Nat.card F) (α : SL(2, F) ≃* SL(2, F))
    (hα : ∀ (ν : Fˣ) (A : SL(2, F)), α (dconj ν A) = dconj ν (α A)) (k : ℕ)
    (hk : ∀ A, (α ^ (2 ^ k)) A = A) : ∀ A, α A = A := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨c₀, hc₀0, hc₀1, hc₀q⟩ := exists_good hF
  set ν₀ : Fˣ := Units.mk0 c₀ hc₀0 with hν₀
  have hν₀1 : (ν₀ : F) ≠ 1 := by rw [hν₀, Units.val_mk0]; exact hc₀1
  set u := sl2Upper F 1 with hu
  set l := sl2Lower F 1 with hl
  have huu : u * u = 1 := by rw [hu, ← sl2Upper_add, ← sl2Upper_zero]; congr 1; linear_combination h2
  have hll : l * l = 1 := by rw [hl, ← sl2Lower_add, ← sl2Lower_zero]; congr 1; linear_combination h2
  have hαinv : ∀ {x : SL(2, F)}, x * x = 1 → α x * α x = 1 := fun h => by rw [← map_mul, h, map_one]
  have hcu : α u * dconj ν₀ (α u) = dconj ν₀ (α u) * α u := by
    rw [← hα, hu, dconj_upper, mul_one, ← map_mul, ← map_mul, ← sl2Upper_add, ← sl2Upper_add,
      add_comm]
  have hl1 : l ≠ 1 := by
    intro h
    have := congrArg (fun M : SL(2, F) => M 1 0) h
    simp [hl] at this
  have hu1 : u ≠ 1 := sl2Upper_one_ne_one
  have hαu : α u = sl2Upper F (α u 0 1) := by
    rcases eq_upper_or_lower (hαinv huu) hν₀1 hcu with h | h
    · exact h
    · exfalso
      set κ := α u 1 0 with hκ
      have hκ0 : κ ≠ 0 := by
        intro h0
        apply hu1
        apply α.injective
        rw [h, h0, sl2Lower_zero, map_one]
      have hform : ∀ {c : F} (hc : c ≠ 0), α (sl2Upper F c) = sl2Lower F (c⁻¹ * κ) := by
        intro c hc
        rw [upper_eq_dconj hc, hα, h, dconj_lower, Units.val_inv_eq_inv_val, Units.val_mk0]
      have hc₀1' : c₀ + 1 ≠ 0 := by
        intro h0
        exact hc₀1 (by linear_combination h0 - h2)
      have hsum := congrArg α (sl2Upper_add c₀ (1 : F))
      rw [map_mul, hform hc₀1', hform hc₀0, hform one_ne_zero, ← sl2Lower_add] at hsum
      have h10 := congrArg (fun M : SL(2, F) => M 1 0) hsum
      simp only [coe_sl2Lower] at h10
      simp at h10
      apply hc₀q
      field_simp at h10
      linear_combination -h10
  set κ := α u 0 1 with hκ
  have hκ0 : κ ≠ 0 := by
    intro h0
    apply hu1
    apply α.injective
    rw [hαu, h0, sl2Upper_zero, map_one]
  have hU : ∀ c, α (sl2Upper F c) = sl2Upper F (c * κ) := by
    intro c
    by_cases hc : c = 0
    · rw [hc, sl2Upper_zero, map_one, zero_mul, sl2Upper_zero]
    · rw [upper_eq_dconj hc, hα, ← hu, hαu, dconj_upper, Units.val_mk0]
  have hcl : α l * dconj ν₀ (α l) = dconj ν₀ (α l) * α l := by
    rw [← hα, hl, dconj_lower, mul_one, ← map_mul, ← map_mul, ← sl2Lower_add, ← sl2Lower_add,
      add_comm]
  have hαl : α l = sl2Lower F (α l 1 0) := by
    rcases eq_upper_or_lower (hαinv hll) hν₀1 hcl with h | h
    · exfalso
      apply hl1
      have h' : α l = α (sl2Upper F (α l 0 1 * κ⁻¹)) := by
        rw [hU, inv_mul_cancel_right₀ hκ0, ← h]
      have := α.injective h'
      have h10 := congrArg (fun M : SL(2, F) => M 1 0) this
      simp [hl] at h10
    · exact h
  set κ' := α l 1 0 with hκ'
  have hL : ∀ c, α (sl2Lower F c) = sl2Lower F (c * κ') := by
    intro c
    by_cases hc : c = 0
    · rw [hc, sl2Lower_zero, map_one, zero_mul, sl2Lower_zero]
    · rw [lower_eq_dconj hc, hα, ← hl, hαl, dconj_lower, inv_inv, Units.val_mk0]
  have hκκ' : κ * κ' = 1 := by
    have h3 := congrArg α (upper_mul_lower_pow_three (F := F))
    rw [map_pow, map_mul, map_one, ← hu, ← hl, hαu, hαl] at h3
    have h01 := congrArg (fun M : SL(2, F) => M 0 1) h3
    rw [upper_mul_lower_pow_three_zero_one, h2] at h01
    simp only [zero_mul, add_zero] at h01
    have hsq : (1 + κ * κ') ^ 2 = 0 := by
      rcases mul_eq_zero.mp h01 with h | h
      · exact absurd h hκ0
      · exact h
    have h1 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
    linear_combination h1 - h2
  have hpowU : ∀ n : ℕ, (α ^ n) u = sl2Upper F (κ ^ n) := by
    intro n
    induction n with
    | zero => simp [hu]
    | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hU, pow_succ]
  have hκ1 : κ = 1 := by
    have h1 := hpowU (2 ^ k)
    rw [hk] at h1
    have h01 := congrArg (fun M : SL(2, F) => M 0 1) h1
    simp [hu] at h01
    have hinj : ∀ m : ℕ, ∀ x y : F, x ^ 2 ^ m = y ^ 2 ^ m → x = y := by
      intro m
      induction m with
      | zero => intro x y h; simpa using h
      | succ m ih =>
        intro x y h
        apply ih
        apply CharTwo.sq_injective
        show (x ^ 2 ^ m) ^ 2 = (y ^ 2 ^ m) ^ 2
        rw [← pow_mul, ← pow_mul, ← pow_succ]
        exact h
    exact hinj k κ 1 (by rw [one_pow]; simpa using h01.symm)
  have hκ'1 : κ' = 1 := by rw [hκ1, one_mul] at hκκ'; exact hκκ'
  intro A
  have hle : Subgroup.closure (Set.range (sl2Upper F) ∪ Set.range (sl2Lower F)) ≤
      MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id _) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change α (sl2Upper F c) = sl2Upper F c
      rw [hU, hκ1, mul_one]
    · change α (sl2Lower F c) = sl2Lower F c
      rw [hL, hκ'1, mul_one]
  rw [sl2_closure_upper_lower] at hle
  exact hle (Subgroup.mem_top A)

end CharTwo

end CFSG.StandardType.KGCentSL2

end
